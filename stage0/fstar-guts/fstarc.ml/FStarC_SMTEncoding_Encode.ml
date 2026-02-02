open Prims
type encoding_depth = (Prims.int * Prims.int)
let dbg_SMTEncoding : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "SMTEncoding"
let dbg_SMTQuery : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "SMTQuery"
let dbg_Time : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Time"
let norm_before_encoding (env : FStarC_SMTEncoding_Env.env_t)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let steps =
    [FStarC_TypeChecker_Env.Eager_unfolding;
    FStarC_TypeChecker_Env.Simplify;
    FStarC_TypeChecker_Env.Primops;
    FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta] in
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_TypeChecker_Env.current_module
          env.FStarC_SMTEncoding_Env.tcenv in
      FStarC_Ident.string_of_lid uu___2 in
    FStar_Pervasives_Native.Some uu___1 in
  FStarC_Profiling.profile
    (fun uu___1 ->
       FStarC_TypeChecker_Normalize.normalize steps
         env.FStarC_SMTEncoding_Env.tcenv t) uu___
    "FStarC.SMTEncoding.Encode.norm_before_encoding"
let norm_before_encoding_us (env : FStarC_SMTEncoding_Env.env_t)
  (us : FStarC_Syntax_Syntax.univ_names) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  let env_u =
    let uu___ =
      FStarC_TypeChecker_Env.push_univ_vars env.FStarC_SMTEncoding_Env.tcenv
        us in
    {
      FStarC_SMTEncoding_Env.bvar_bindings =
        (env.FStarC_SMTEncoding_Env.bvar_bindings);
      FStarC_SMTEncoding_Env.fvar_bindings =
        (env.FStarC_SMTEncoding_Env.fvar_bindings);
      FStarC_SMTEncoding_Env.depth = (env.FStarC_SMTEncoding_Env.depth);
      FStarC_SMTEncoding_Env.tcenv = uu___;
      FStarC_SMTEncoding_Env.warn = (env.FStarC_SMTEncoding_Env.warn);
      FStarC_SMTEncoding_Env.nolabels = (env.FStarC_SMTEncoding_Env.nolabels);
      FStarC_SMTEncoding_Env.use_zfuel_name =
        (env.FStarC_SMTEncoding_Env.use_zfuel_name);
      FStarC_SMTEncoding_Env.encode_non_total_function_typ =
        (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
      FStarC_SMTEncoding_Env.current_module_name =
        (env.FStarC_SMTEncoding_Env.current_module_name);
      FStarC_SMTEncoding_Env.encoding_quantifier =
        (env.FStarC_SMTEncoding_Env.encoding_quantifier);
      FStarC_SMTEncoding_Env.global_cache =
        (env.FStarC_SMTEncoding_Env.global_cache)
    } in
  let uu___ = FStarC_Syntax_Subst.open_univ_vars us t in
  match uu___ with
  | (us1, t1) ->
      let t2 = norm_before_encoding env_u t1 in
      FStarC_Syntax_Subst.close_univ_vars us1 t2
let norm_with_steps (steps : FStarC_TypeChecker_Env.steps)
  (env : FStarC_TypeChecker_Env.env) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_TypeChecker_Env.current_module env in
      FStarC_Ident.string_of_lid uu___2 in
    FStar_Pervasives_Native.Some uu___1 in
  FStarC_Profiling.profile
    (fun uu___1 -> FStarC_TypeChecker_Normalize.normalize steps env t) uu___
    "FStarC.SMTEncoding.Encode.norm"
type prims_t =
  {
  mk:
    FStarC_Ident.lident ->
      Prims.string ->
        (FStarC_SMTEncoding_Term.term * Prims.int *
          FStarC_SMTEncoding_Term.decl Prims.list)
    ;
  is: FStarC_Ident.lident -> Prims.bool }
let __proj__Mkprims_t__item__mk (projectee : prims_t) :
  FStarC_Ident.lident ->
    Prims.string ->
      (FStarC_SMTEncoding_Term.term * Prims.int *
        FStarC_SMTEncoding_Term.decl Prims.list)=
  match projectee with | { mk; is;_} -> mk
let __proj__Mkprims_t__item__is (projectee : prims_t) :
  FStarC_Ident.lident -> Prims.bool= match projectee with | { mk; is;_} -> is
type defn_rel_type =
  | Eq 
  | ValidIff 
let uu___is_Eq (projectee : defn_rel_type) : Prims.bool=
  match projectee with | Eq -> true | uu___ -> false
let uu___is_ValidIff (projectee : defn_rel_type) : Prims.bool=
  match projectee with | ValidIff -> true | uu___ -> false
let rel_type_f (uu___ : defn_rel_type) :
  (FStarC_SMTEncoding_Term.term * FStarC_SMTEncoding_Term.term) ->
    FStarC_SMTEncoding_Term.term=
  match uu___ with
  | Eq -> FStarC_SMTEncoding_Util.mkEq
  | ValidIff ->
      (fun uu___1 ->
         match uu___1 with
         | (x, y) ->
             let uu___2 =
               let uu___3 = FStarC_SMTEncoding_Term.mk_Valid x in (uu___3, y) in
             FStarC_SMTEncoding_Util.mkEq uu___2)
let prims : prims_t=
  let module_name = "Prims" in
  let uu___ =
    FStarC_SMTEncoding_Env.fresh_fvar module_name "a"
      FStarC_SMTEncoding_Term.Term_sort in
  match uu___ with
  | (asym, a) ->
      let uu___1 =
        FStarC_SMTEncoding_Env.fresh_fvar module_name "x"
          FStarC_SMTEncoding_Term.Term_sort in
      (match uu___1 with
       | (xsym, x) ->
           let uu___2 =
             FStarC_SMTEncoding_Env.fresh_fvar module_name "y"
               FStarC_SMTEncoding_Term.Term_sort in
           (match uu___2 with
            | (ysym, y) ->
                let quant_with_pre rel vars precondition body rng x1 =
                  let xname_decl =
                    let uu___3 =
                      let uu___4 =
                        FStarC_List.map FStarC_SMTEncoding_Term.fv_sort vars in
                      (x1, uu___4, FStarC_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStarC_SMTEncoding_Term.DeclFun uu___3 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStarC_SMTEncoding_Term.DeclFun
                      (xtok, [], FStarC_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu___3 =
                      let uu___4 =
                        FStarC_List.map FStarC_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu___4) in
                    FStarC_SMTEncoding_Util.mkApp uu___3 in
                  let xtok1 = FStarC_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app =
                    FStarC_SMTEncoding_EncodeTerm.mk_Apply xtok1 vars in
                  let tot_fun_axioms =
                    let all_vars_but_one =
                      FStar_Pervasives_Native.fst (FStarC_Util.prefix vars) in
                    let axiom_name = Prims.strcat "primitive_tot_fun_" x1 in
                    let tot_fun_axiom_for_x =
                      let uu___3 =
                        let uu___4 =
                          FStarC_SMTEncoding_Term.mk_IsTotFun xtok1 in
                        (uu___4, FStar_Pervasives_Native.None, axiom_name) in
                      FStarC_SMTEncoding_Util.mkAssume uu___3 in
                    let uu___3 =
                      FStarC_List.fold_left
                        (fun uu___4 var ->
                           match uu___4 with
                           | (axioms, app, vars1) ->
                               let app1 =
                                 FStarC_SMTEncoding_EncodeTerm.mk_Apply app
                                   [var] in
                               let vars2 = FStarC_List.op_At vars1 [var] in
                               let axiom_name1 =
                                 let uu___5 =
                                   let uu___6 =
                                     FStarC_Class_Show.show
                                       FStarC_Class_Show.showable_nat
                                       (FStarC_List.length vars2) in
                                   Prims.strcat "." uu___6 in
                                 Prims.strcat axiom_name uu___5 in
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     let uu___8 =
                                       let uu___9 =
                                         let uu___10 =
                                           FStarC_SMTEncoding_Term.mk_IsTotFun
                                             app1 in
                                         ([[app1]], vars2, uu___10) in
                                       FStarC_SMTEncoding_Term.mkForall rng
                                         uu___9 in
                                     (uu___8, FStar_Pervasives_Native.None,
                                       axiom_name1) in
                                   FStarC_SMTEncoding_Util.mkAssume uu___7 in
                                 uu___6 :: axioms in
                               (uu___5, app1, vars2))
                        ([tot_fun_axiom_for_x], xtok1, []) all_vars_but_one in
                    match uu___3 with
                    | (axioms, uu___4, uu___5) -> FStarC_List.rev axioms in
                  let rel_body =
                    let rel_body1 = rel_type_f rel (xapp, body) in
                    match precondition with
                    | FStar_Pervasives_Native.None -> rel_body1
                    | FStar_Pervasives_Native.Some pre ->
                        FStarC_SMTEncoding_Util.mkImp (pre, rel_body1) in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                FStarC_SMTEncoding_Term.mkForall rng
                                  ([[xapp]], vars, rel_body) in
                              (uu___9, FStar_Pervasives_Native.None,
                                (Prims.strcat "primitive_" x1)) in
                            FStarC_SMTEncoding_Util.mkAssume uu___8 in
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
                                  FStarC_SMTEncoding_Util.mkEq
                                    (xtok_app, xapp) in
                                ([[xtok_app]], vars, uu___11) in
                              FStarC_SMTEncoding_Term.mkForall rng uu___10 in
                            (uu___9,
                              (FStar_Pervasives_Native.Some
                                 "Name-token correspondence"),
                              (Prims.strcat "token_correspondence_" x1)) in
                          FStarC_SMTEncoding_Util.mkAssume uu___8 in
                        [uu___7] in
                      FStarC_List.op_At tot_fun_axioms uu___6 in
                    FStarC_List.op_At uu___4 uu___5 in
                  (xtok1, (FStarC_List.length vars), uu___3) in
                let quant rel vars body =
                  quant_with_pre rel vars FStar_Pervasives_Native.None body in
                let axy =
                  FStarC_List.map FStarC_SMTEncoding_Term.mk_fv
                    [(asym, FStarC_SMTEncoding_Term.Term_sort);
                    (xsym, FStarC_SMTEncoding_Term.Term_sort);
                    (ysym, FStarC_SMTEncoding_Term.Term_sort)] in
                let xy =
                  FStarC_List.map FStarC_SMTEncoding_Term.mk_fv
                    [(xsym, FStarC_SMTEncoding_Term.Term_sort);
                    (ysym, FStarC_SMTEncoding_Term.Term_sort)] in
                let qx =
                  FStarC_List.map FStarC_SMTEncoding_Term.mk_fv
                    [(xsym, FStarC_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStarC_SMTEncoding_Util.mkEq (x, y) in
                        FStarC_SMTEncoding_Term.boxBool uu___6 in
                      quant Eq axy uu___5 in
                    (FStarC_Parser_Const.op_Eq, uu___4) in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 = FStarC_SMTEncoding_Util.mkEq (x, y) in
                            FStarC_SMTEncoding_Util.mkNot uu___9 in
                          FStarC_SMTEncoding_Term.boxBool uu___8 in
                        quant Eq axy uu___7 in
                      (FStarC_Parser_Const.op_notEq, uu___6) in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            let uu___10 =
                              let uu___11 =
                                let uu___12 =
                                  FStarC_SMTEncoding_Term.unboxBool x in
                                let uu___13 =
                                  FStarC_SMTEncoding_Term.unboxBool y in
                                (uu___12, uu___13) in
                              FStarC_SMTEncoding_Util.mkAnd uu___11 in
                            FStarC_SMTEncoding_Term.boxBool uu___10 in
                          quant Eq xy uu___9 in
                        (FStarC_Parser_Const.op_And, uu___8) in
                      let uu___8 =
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              let uu___12 =
                                let uu___13 =
                                  let uu___14 =
                                    FStarC_SMTEncoding_Term.unboxBool x in
                                  let uu___15 =
                                    FStarC_SMTEncoding_Term.unboxBool y in
                                  (uu___14, uu___15) in
                                FStarC_SMTEncoding_Util.mkOr uu___13 in
                              FStarC_SMTEncoding_Term.boxBool uu___12 in
                            quant Eq xy uu___11 in
                          (FStarC_Parser_Const.op_Or, uu___10) in
                        let uu___10 =
                          let uu___11 =
                            let uu___12 =
                              let uu___13 =
                                let uu___14 =
                                  let uu___15 =
                                    FStarC_SMTEncoding_Term.unboxBool x in
                                  FStarC_SMTEncoding_Util.mkNot uu___15 in
                                FStarC_SMTEncoding_Term.boxBool uu___14 in
                              quant Eq qx uu___13 in
                            (FStarC_Parser_Const.op_Negation, uu___12) in
                          let uu___12 =
                            let uu___13 =
                              let uu___14 =
                                let uu___15 =
                                  let uu___16 =
                                    let uu___17 =
                                      let uu___18 =
                                        FStarC_SMTEncoding_Term.unboxInt x in
                                      let uu___19 =
                                        FStarC_SMTEncoding_Term.unboxInt y in
                                      (uu___18, uu___19) in
                                    FStarC_SMTEncoding_Util.mkLT uu___17 in
                                  FStarC_SMTEncoding_Term.boxBool uu___16 in
                                quant Eq xy uu___15 in
                              (FStarC_Parser_Const.op_LT, uu___14) in
                            let uu___14 =
                              let uu___15 =
                                let uu___16 =
                                  let uu___17 =
                                    let uu___18 =
                                      let uu___19 =
                                        let uu___20 =
                                          FStarC_SMTEncoding_Term.unboxInt x in
                                        let uu___21 =
                                          FStarC_SMTEncoding_Term.unboxInt y in
                                        (uu___20, uu___21) in
                                      FStarC_SMTEncoding_Util.mkLTE uu___19 in
                                    FStarC_SMTEncoding_Term.boxBool uu___18 in
                                  quant Eq xy uu___17 in
                                (FStarC_Parser_Const.op_LTE, uu___16) in
                              let uu___16 =
                                let uu___17 =
                                  let uu___18 =
                                    let uu___19 =
                                      let uu___20 =
                                        let uu___21 =
                                          let uu___22 =
                                            FStarC_SMTEncoding_Term.unboxInt
                                              x in
                                          let uu___23 =
                                            FStarC_SMTEncoding_Term.unboxInt
                                              y in
                                          (uu___22, uu___23) in
                                        FStarC_SMTEncoding_Util.mkGT uu___21 in
                                      FStarC_SMTEncoding_Term.boxBool uu___20 in
                                    quant Eq xy uu___19 in
                                  (FStarC_Parser_Const.op_GT, uu___18) in
                                let uu___18 =
                                  let uu___19 =
                                    let uu___20 =
                                      let uu___21 =
                                        let uu___22 =
                                          let uu___23 =
                                            let uu___24 =
                                              FStarC_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu___25 =
                                              FStarC_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu___24, uu___25) in
                                          FStarC_SMTEncoding_Util.mkGTE
                                            uu___23 in
                                        FStarC_SMTEncoding_Term.boxBool
                                          uu___22 in
                                      quant Eq xy uu___21 in
                                    (FStarC_Parser_Const.op_GTE, uu___20) in
                                  let uu___20 =
                                    let uu___21 =
                                      let uu___22 =
                                        let uu___23 =
                                          let uu___24 =
                                            let uu___25 =
                                              let uu___26 =
                                                FStarC_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu___27 =
                                                FStarC_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu___26, uu___27) in
                                            FStarC_SMTEncoding_Util.mkSub
                                              uu___25 in
                                          FStarC_SMTEncoding_Term.boxInt
                                            uu___24 in
                                        quant Eq xy uu___23 in
                                      (FStarC_Parser_Const.op_Subtraction,
                                        uu___22) in
                                    let uu___22 =
                                      let uu___23 =
                                        let uu___24 =
                                          let uu___25 =
                                            let uu___26 =
                                              let uu___27 =
                                                FStarC_SMTEncoding_Term.unboxInt
                                                  x in
                                              FStarC_SMTEncoding_Util.mkMinus
                                                uu___27 in
                                            FStarC_SMTEncoding_Term.boxInt
                                              uu___26 in
                                          quant Eq qx uu___25 in
                                        (FStarC_Parser_Const.op_Minus,
                                          uu___24) in
                                      let uu___24 =
                                        let uu___25 =
                                          let uu___26 =
                                            let uu___27 =
                                              let uu___28 =
                                                let uu___29 =
                                                  let uu___30 =
                                                    FStarC_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu___31 =
                                                    FStarC_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu___30, uu___31) in
                                                FStarC_SMTEncoding_Util.mkAdd
                                                  uu___29 in
                                              FStarC_SMTEncoding_Term.boxInt
                                                uu___28 in
                                            quant Eq xy uu___27 in
                                          (FStarC_Parser_Const.op_Addition,
                                            uu___26) in
                                        let uu___26 =
                                          let uu___27 =
                                            let uu___28 =
                                              let uu___29 =
                                                let uu___30 =
                                                  let uu___31 =
                                                    let uu___32 =
                                                      FStarC_SMTEncoding_Term.unboxInt
                                                        x in
                                                    let uu___33 =
                                                      FStarC_SMTEncoding_Term.unboxInt
                                                        y in
                                                    (uu___32, uu___33) in
                                                  FStarC_SMTEncoding_Util.mkMul
                                                    uu___31 in
                                                FStarC_SMTEncoding_Term.boxInt
                                                  uu___30 in
                                              quant Eq xy uu___29 in
                                            (FStarC_Parser_Const.op_Multiply,
                                              uu___28) in
                                          let uu___28 =
                                            let uu___29 =
                                              let uu___30 =
                                                let uu___31 =
                                                  let uu___32 =
                                                    let uu___33 =
                                                      let uu___34 =
                                                        let uu___35 =
                                                          FStarC_SMTEncoding_Term.unboxInt
                                                            y in
                                                        let uu___36 =
                                                          FStarC_SMTEncoding_Util.mkInteger
                                                            "0" in
                                                        (uu___35, uu___36) in
                                                      FStarC_SMTEncoding_Util.mkEq
                                                        uu___34 in
                                                    FStarC_SMTEncoding_Util.mkNot
                                                      uu___33 in
                                                  FStar_Pervasives_Native.Some
                                                    uu___32 in
                                                let uu___32 =
                                                  let uu___33 =
                                                    let uu___34 =
                                                      let uu___35 =
                                                        FStarC_SMTEncoding_Term.unboxInt
                                                          x in
                                                      let uu___36 =
                                                        FStarC_SMTEncoding_Term.unboxInt
                                                          y in
                                                      (uu___35, uu___36) in
                                                    FStarC_SMTEncoding_Util.mkDiv
                                                      uu___34 in
                                                  FStarC_SMTEncoding_Term.boxInt
                                                    uu___33 in
                                                quant_with_pre Eq xy uu___31
                                                  uu___32 in
                                              (FStarC_Parser_Const.op_Division,
                                                uu___30) in
                                            let uu___30 =
                                              let uu___31 =
                                                let uu___32 =
                                                  let uu___33 =
                                                    let uu___34 =
                                                      let uu___35 =
                                                        let uu___36 =
                                                          let uu___37 =
                                                            FStarC_SMTEncoding_Term.unboxInt
                                                              y in
                                                          let uu___38 =
                                                            FStarC_SMTEncoding_Util.mkInteger
                                                              "0" in
                                                          (uu___37, uu___38) in
                                                        FStarC_SMTEncoding_Util.mkEq
                                                          uu___36 in
                                                      FStarC_SMTEncoding_Util.mkNot
                                                        uu___35 in
                                                    FStar_Pervasives_Native.Some
                                                      uu___34 in
                                                  let uu___34 =
                                                    let uu___35 =
                                                      let uu___36 =
                                                        let uu___37 =
                                                          FStarC_SMTEncoding_Term.unboxInt
                                                            x in
                                                        let uu___38 =
                                                          FStarC_SMTEncoding_Term.unboxInt
                                                            y in
                                                        (uu___37, uu___38) in
                                                      FStarC_SMTEncoding_Util.mkMod
                                                        uu___36 in
                                                    FStarC_SMTEncoding_Term.boxInt
                                                      uu___35 in
                                                  quant_with_pre Eq xy
                                                    uu___33 uu___34 in
                                                (FStarC_Parser_Const.op_Modulus,
                                                  uu___32) in
                                              let uu___32 =
                                                let uu___33 =
                                                  let uu___34 =
                                                    let uu___35 =
                                                      let uu___36 =
                                                        let uu___37 =
                                                          FStarC_SMTEncoding_Term.unboxReal
                                                            x in
                                                        let uu___38 =
                                                          FStarC_SMTEncoding_Term.unboxReal
                                                            y in
                                                        (uu___37, uu___38) in
                                                      FStarC_SMTEncoding_Util.mkLT
                                                        uu___36 in
                                                    quant ValidIff xy uu___35 in
                                                  (FStarC_Parser_Const.real_op_LT,
                                                    uu___34) in
                                                let uu___34 =
                                                  let uu___35 =
                                                    let uu___36 =
                                                      let uu___37 =
                                                        let uu___38 =
                                                          let uu___39 =
                                                            FStarC_SMTEncoding_Term.unboxReal
                                                              x in
                                                          let uu___40 =
                                                            FStarC_SMTEncoding_Term.unboxReal
                                                              y in
                                                          (uu___39, uu___40) in
                                                        FStarC_SMTEncoding_Util.mkLTE
                                                          uu___38 in
                                                      quant ValidIff xy
                                                        uu___37 in
                                                    (FStarC_Parser_Const.real_op_LTE,
                                                      uu___36) in
                                                  let uu___36 =
                                                    let uu___37 =
                                                      let uu___38 =
                                                        let uu___39 =
                                                          let uu___40 =
                                                            let uu___41 =
                                                              FStarC_SMTEncoding_Term.unboxReal
                                                                x in
                                                            let uu___42 =
                                                              FStarC_SMTEncoding_Term.unboxReal
                                                                y in
                                                            (uu___41,
                                                              uu___42) in
                                                          FStarC_SMTEncoding_Util.mkGT
                                                            uu___40 in
                                                        quant ValidIff xy
                                                          uu___39 in
                                                      (FStarC_Parser_Const.real_op_GT,
                                                        uu___38) in
                                                    let uu___38 =
                                                      let uu___39 =
                                                        let uu___40 =
                                                          let uu___41 =
                                                            let uu___42 =
                                                              let uu___43 =
                                                                FStarC_SMTEncoding_Term.unboxReal
                                                                  x in
                                                              let uu___44 =
                                                                FStarC_SMTEncoding_Term.unboxReal
                                                                  y in
                                                              (uu___43,
                                                                uu___44) in
                                                            FStarC_SMTEncoding_Util.mkGTE
                                                              uu___42 in
                                                          quant ValidIff xy
                                                            uu___41 in
                                                        (FStarC_Parser_Const.real_op_GTE,
                                                          uu___40) in
                                                      let uu___40 =
                                                        let uu___41 =
                                                          let uu___42 =
                                                            let uu___43 =
                                                              let uu___44 =
                                                                let uu___45 =
                                                                  let uu___46
                                                                    =
                                                                    FStarC_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                  let uu___47
                                                                    =
                                                                    FStarC_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                  (uu___46,
                                                                    uu___47) in
                                                                FStarC_SMTEncoding_Util.mkSub
                                                                  uu___45 in
                                                              FStarC_SMTEncoding_Term.boxReal
                                                                uu___44 in
                                                            quant Eq xy
                                                              uu___43 in
                                                          (FStarC_Parser_Const.real_op_Subtraction,
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
                                                                    FStarC_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                    let uu___49
                                                                    =
                                                                    FStarC_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu___48,
                                                                    uu___49) in
                                                                  FStarC_SMTEncoding_Util.mkAdd
                                                                    uu___47 in
                                                                FStarC_SMTEncoding_Term.boxReal
                                                                  uu___46 in
                                                              quant Eq xy
                                                                uu___45 in
                                                            (FStarC_Parser_Const.real_op_Addition,
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
                                                                    FStarC_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                    let uu___51
                                                                    =
                                                                    FStarC_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu___50,
                                                                    uu___51) in
                                                                    FStarC_SMTEncoding_Util.mkMul
                                                                    uu___49 in
                                                                  FStarC_SMTEncoding_Term.boxReal
                                                                    uu___48 in
                                                                quant Eq xy
                                                                  uu___47 in
                                                              (FStarC_Parser_Const.real_op_Multiply,
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
                                                                    let uu___53
                                                                    =
                                                                    FStarC_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    let uu___54
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkReal
                                                                    "0" in
                                                                    (uu___53,
                                                                    uu___54) in
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    uu___52 in
                                                                    FStarC_SMTEncoding_Util.mkNot
                                                                    uu___51 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___50 in
                                                                  let uu___50
                                                                    =
                                                                    let uu___51
                                                                    =
                                                                    let uu___52
                                                                    =
                                                                    let uu___53
                                                                    =
                                                                    FStarC_SMTEncoding_Term.unboxReal
                                                                    x in
                                                                    let uu___54
                                                                    =
                                                                    FStarC_SMTEncoding_Term.unboxReal
                                                                    y in
                                                                    (uu___53,
                                                                    uu___54) in
                                                                    FStarC_SMTEncoding_Util.mkRealDiv
                                                                    uu___52 in
                                                                    FStarC_SMTEncoding_Term.boxReal
                                                                    uu___51 in
                                                                  quant_with_pre
                                                                    Eq xy
                                                                    uu___49
                                                                    uu___50 in
                                                                (FStarC_Parser_Const.real_op_Division,
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
                                                                    FStarC_SMTEncoding_Term.unboxInt
                                                                    x in
                                                                    FStarC_SMTEncoding_Term.mkRealOfInt
                                                                    uu___53
                                                                    FStarC_Range_Type.dummyRange in
                                                                    FStarC_SMTEncoding_Term.boxReal
                                                                    uu___52 in
                                                                    quant Eq
                                                                    qx
                                                                    uu___51 in
                                                                  (FStarC_Parser_Const.real_of_int,
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
                      FStarC_List.find
                        (fun uu___5 ->
                           match uu___5 with
                           | (l', uu___6) -> FStarC_Ident.lid_equals l l')
                        prims1 in
                    FStarC_Option.map
                      (fun uu___5 ->
                         match uu___5 with
                         | (uu___6, b) ->
                             let uu___7 = FStarC_Ident.range_of_lid l in
                             b uu___7 v) uu___4 in
                  FStarC_Option.must uu___3 in
                let is l =
                  FStarC_Util.for_some
                    (fun uu___3 ->
                       match uu___3 with
                       | (l', uu___4) -> FStarC_Ident.lid_equals l l') prims1 in
                { mk; is }))
let pretype_axiom (term_constr_eq : Prims.bool) (rng : FStarC_Range_Type.t)
  (env : FStarC_SMTEncoding_Env.env_t) (tapp : FStarC_SMTEncoding_Term.term)
  (vars : FStarC_SMTEncoding_Term.fv Prims.list) :
  FStarC_SMTEncoding_Term.decl=
  let uu___ =
    FStarC_SMTEncoding_Env.fresh_fvar
      env.FStarC_SMTEncoding_Env.current_module_name "x"
      FStarC_SMTEncoding_Term.Term_sort in
  match uu___ with
  | (xxsym, xx) ->
      let uu___1 =
        FStarC_SMTEncoding_Env.fresh_fvar
          env.FStarC_SMTEncoding_Env.current_module_name "f"
          FStarC_SMTEncoding_Term.Fuel_sort in
      (match uu___1 with
       | (ffsym, ff) ->
           let xx_has_type =
             FStarC_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
           let tapp_hash = FStarC_SMTEncoding_Term.hash_of_term tapp in
           let module_name = env.FStarC_SMTEncoding_Env.current_module_name in
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     FStarC_SMTEncoding_Term.mk_fv
                       (xxsym, FStarC_SMTEncoding_Term.Term_sort) in
                   let uu___7 =
                     let uu___8 =
                       FStarC_SMTEncoding_Term.mk_fv
                         (ffsym, FStarC_SMTEncoding_Term.Fuel_sort) in
                     uu___8 :: vars in
                   uu___6 :: uu___7 in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       if term_constr_eq
                       then
                         let uu___9 =
                           let uu___10 =
                             FStarC_SMTEncoding_Util.mkApp
                               ("Term_constr_id", [tapp]) in
                           let uu___11 =
                             let uu___12 =
                               let uu___13 =
                                 let uu___14 =
                                   FStarC_SMTEncoding_Util.mkApp
                                     ("PreType", [xx]) in
                                 [uu___14] in
                               ("Term_constr_id", uu___13) in
                             FStarC_SMTEncoding_Util.mkApp uu___12 in
                           (uu___10, uu___11) in
                         FStarC_SMTEncoding_Util.mkEq uu___9
                       else
                         (let uu___10 =
                            let uu___11 =
                              FStarC_SMTEncoding_Util.mkApp ("PreType", [xx]) in
                            (tapp, uu___11) in
                          FStarC_SMTEncoding_Util.mkEq uu___10) in
                     (xx_has_type, uu___8) in
                   FStarC_SMTEncoding_Util.mkImp uu___7 in
                 ([[xx_has_type]], uu___5, uu___6) in
               FStarC_SMTEncoding_Term.mkForall rng uu___4 in
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   let uu___7 = FStarC_Util.digest_of_string tapp_hash in
                   Prims.strcat "_pretyping_" uu___7 in
                 Prims.strcat module_name uu___6 in
               FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.mk_unique
                 uu___5 in
             (uu___3, (FStar_Pervasives_Native.Some "pretyping"), uu___4) in
           FStarC_SMTEncoding_Util.mkAssume uu___2)
let primitive_type_axioms :
  FStarC_TypeChecker_Env.env ->
    FStarC_Ident.lident ->
      Prims.string ->
        FStarC_SMTEncoding_Term.term ->
          FStarC_SMTEncoding_Term.decl Prims.list=
  let xx =
    FStarC_SMTEncoding_Term.mk_fv ("x", FStarC_SMTEncoding_Term.Term_sort) in
  let x = FStarC_SMTEncoding_Util.mkFreeV xx in
  let yy =
    FStarC_SMTEncoding_Term.mk_fv ("y", FStarC_SMTEncoding_Term.Term_sort) in
  let y = FStarC_SMTEncoding_Util.mkFreeV yy in
  let mkForall_fuel env =
    let uu___ =
      let uu___1 = FStarC_TypeChecker_Env.current_module env in
      FStarC_Ident.string_of_lid uu___1 in
    FStarC_SMTEncoding_EncodeTerm.mkForall_fuel uu___ in
  let mk_unit env nm tt =
    let typing_pred = FStarC_SMTEncoding_Term.mk_HasType x tt in
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_SMTEncoding_Term.mk_HasType
            FStarC_SMTEncoding_Term.mk_Term_unit tt in
        (uu___2, (FStar_Pervasives_Native.Some "unit typing"), "unit_typing") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStarC_SMTEncoding_Util.mkEq
                      (x, FStarC_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu___8) in
                FStarC_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStarC_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStarC_SMTEncoding_Util.mkAssume uu___3 in
      [uu___2] in
    uu___ :: uu___1 in
  let mk_bool env nm tt =
    let typing_pred = FStarC_SMTEncoding_Term.mk_HasType x tt in
    let bb =
      FStarC_SMTEncoding_Term.mk_fv ("b", FStarC_SMTEncoding_Term.Bool_sort) in
    let b = FStarC_SMTEncoding_Util.mkFreeV bb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_SMTEncoding_Term.boxBool b in [uu___7] in
              [uu___6] in
            let uu___6 =
              let uu___7 = FStarC_SMTEncoding_Term.boxBool b in
              FStarC_SMTEncoding_Term.mk_HasType uu___7 tt in
            (uu___5, [bb], uu___6) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "bool typing"), "bool_typing") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStarC_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStarC_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu___8) in
                FStarC_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStarC_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStarC_SMTEncoding_Util.mkAssume uu___3 in
      [uu___2] in
    uu___ :: uu___1 in
  let mk_int env nm tt =
    let lex_t =
      let uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Ident.string_of_lid FStarC_Parser_Const.lex_t_lid in
          (uu___2, FStarC_SMTEncoding_Term.Term_sort) in
        FStarC_SMTEncoding_Term.mk_fv uu___1 in
      FStarC_SMTEncoding_Util.mkFreeV uu___ in
    let typing_pred = FStarC_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStarC_SMTEncoding_Term.mk_HasType y tt in
    let aa =
      FStarC_SMTEncoding_Term.mk_fv ("a", FStarC_SMTEncoding_Term.Int_sort) in
    let a = FStarC_SMTEncoding_Util.mkFreeV aa in
    let bb =
      FStarC_SMTEncoding_Term.mk_fv ("b", FStarC_SMTEncoding_Term.Int_sort) in
    let b = FStarC_SMTEncoding_Util.mkFreeV bb in
    let precedes_y_x =
      let uu___ =
        FStarC_SMTEncoding_Util.mkApp
          ("Prims.precedes",
            [FStarC_SMTEncoding_Term.mk_U_zero;
            FStarC_SMTEncoding_Term.mk_U_zero;
            lex_t;
            lex_t;
            y;
            x]) in
      FStarC_SMTEncoding_Term.mk_Valid uu___ in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_SMTEncoding_Term.boxInt b in [uu___7] in
              [uu___6] in
            let uu___6 =
              let uu___7 = FStarC_SMTEncoding_Term.boxInt b in
              FStarC_SMTEncoding_Term.mk_HasType uu___7 tt in
            (uu___5, [bb], uu___6) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "int typing"), "int_typing") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStarC_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStarC_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu___8) in
                FStarC_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStarC_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStarC_SMTEncoding_Util.mkAssume uu___3 in
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
                                  FStarC_SMTEncoding_Term.unboxInt x in
                                let uu___17 =
                                  FStarC_SMTEncoding_Util.mkInteger'
                                    Prims.int_zero in
                                (uu___16, uu___17) in
                              FStarC_SMTEncoding_Util.mkGT uu___15 in
                            let uu___15 =
                              let uu___16 =
                                let uu___17 =
                                  let uu___18 =
                                    FStarC_SMTEncoding_Term.unboxInt y in
                                  let uu___19 =
                                    FStarC_SMTEncoding_Util.mkInteger'
                                      Prims.int_zero in
                                  (uu___18, uu___19) in
                                FStarC_SMTEncoding_Util.mkGTE uu___17 in
                              let uu___17 =
                                let uu___18 =
                                  let uu___19 =
                                    let uu___20 =
                                      FStarC_SMTEncoding_Term.unboxInt y in
                                    let uu___21 =
                                      FStarC_SMTEncoding_Term.unboxInt x in
                                    (uu___20, uu___21) in
                                  FStarC_SMTEncoding_Util.mkLT uu___19 in
                                [uu___18] in
                              uu___16 :: uu___17 in
                            uu___14 :: uu___15 in
                          typing_pred_y :: uu___13 in
                        typing_pred :: uu___12 in
                      FStarC_SMTEncoding_Util.mk_and_l uu___11 in
                    (uu___10, precedes_y_x) in
                  FStarC_SMTEncoding_Util.mkImp uu___9 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu___8) in
              let uu___8 =
                let uu___9 = FStarC_TypeChecker_Env.get_range env in
                let uu___10 = mkForall_fuel env in uu___10 uu___9 in
              uu___8 uu___7 in
            (uu___6,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStarC_SMTEncoding_Util.mkAssume uu___5 in
        [uu___4] in
      uu___2 :: uu___3 in
    uu___ :: uu___1 in
  let mk_real env nm tt =
    let typing_pred = FStarC_SMTEncoding_Term.mk_HasType x tt in
    let aa =
      FStarC_SMTEncoding_Term.mk_fv
        ("a", (FStarC_SMTEncoding_Term.Sort "Real")) in
    let a = FStarC_SMTEncoding_Util.mkFreeV aa in
    let bb =
      FStarC_SMTEncoding_Term.mk_fv
        ("b", (FStarC_SMTEncoding_Term.Sort "Real")) in
    let b = FStarC_SMTEncoding_Util.mkFreeV bb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_SMTEncoding_Term.boxReal b in [uu___7] in
              [uu___6] in
            let uu___6 =
              let uu___7 = FStarC_SMTEncoding_Term.boxReal b in
              FStarC_SMTEncoding_Term.mk_HasType uu___7 tt in
            (uu___5, [bb], uu___6) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "real typing"), "real_typing") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStarC_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStarC_SMTEncoding_Term.boxRealFun) x in
                  (typing_pred, uu___8) in
                FStarC_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStarC_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "real inversion"),
            "real_inversion") in
        FStarC_SMTEncoding_Util.mkAssume uu___3 in
      [uu___2] in
    uu___ :: uu___1 in
  let mk_str env nm tt =
    let typing_pred = FStarC_SMTEncoding_Term.mk_HasType x tt in
    let bb =
      FStarC_SMTEncoding_Term.mk_fv
        ("b", FStarC_SMTEncoding_Term.String_sort) in
    let b = FStarC_SMTEncoding_Util.mkFreeV bb in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_SMTEncoding_Term.boxString b in [uu___7] in
              [uu___6] in
            let uu___6 =
              let uu___7 = FStarC_SMTEncoding_Term.boxString b in
              FStarC_SMTEncoding_Term.mk_HasType uu___7 tt in
            (uu___5, [bb], uu___6) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStarC_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStarC_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu___8) in
                FStarC_SMTEncoding_Util.mkImp uu___7 in
              ([[typing_pred]], [xx], uu___6) in
            let uu___6 =
              let uu___7 = FStarC_TypeChecker_Env.get_range env in
              let uu___8 = mkForall_fuel env in uu___8 uu___7 in
            uu___6 uu___5 in
          (uu___4, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStarC_SMTEncoding_Util.mkAssume uu___3 in
      [uu___2] in
    uu___ :: uu___1 in
  let mk_true_interp env nm true_tm =
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    let uu___ =
      FStarC_SMTEncoding_Util.mkAssume
        (valid, (FStar_Pervasives_Native.Some "True interpretation"),
          "true_interp") in
    [uu___] in
  let mk_false_interp env nm false_tm =
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_SMTEncoding_Util.mkIff
            (FStarC_SMTEncoding_Util.mkFalse, valid) in
        (uu___2, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_and_interp env conj uu___ =
    let aa =
      FStarC_SMTEncoding_Term.mk_fv ("a", FStarC_SMTEncoding_Term.Term_sort) in
    let bb =
      FStarC_SMTEncoding_Term.mk_fv ("b", FStarC_SMTEncoding_Term.Term_sort) in
    let a = FStarC_SMTEncoding_Util.mkFreeV aa in
    let b = FStarC_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStarC_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStarC_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStarC_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_TypeChecker_Env.get_range env in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStarC_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu___8, valid) in
              FStarC_SMTEncoding_Util.mkIff uu___7 in
            ([[l_and_a_b]], [aa; bb], uu___6) in
          FStarC_SMTEncoding_Term.mkForall uu___4 uu___5 in
        (uu___3, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStarC_SMTEncoding_Util.mkAssume uu___2 in
    [uu___1] in
  let mk_or_interp env disj uu___ =
    let aa =
      FStarC_SMTEncoding_Term.mk_fv ("a", FStarC_SMTEncoding_Term.Term_sort) in
    let bb =
      FStarC_SMTEncoding_Term.mk_fv ("b", FStarC_SMTEncoding_Term.Term_sort) in
    let a = FStarC_SMTEncoding_Util.mkFreeV aa in
    let b = FStarC_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStarC_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStarC_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStarC_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_TypeChecker_Env.get_range env in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStarC_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu___8, valid) in
              FStarC_SMTEncoding_Util.mkIff uu___7 in
            ([[l_or_a_b]], [aa; bb], uu___6) in
          FStarC_SMTEncoding_Term.mkForall uu___4 uu___5 in
        (uu___3, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStarC_SMTEncoding_Util.mkAssume uu___2 in
    [uu___1] in
  let mk_eq2_interp env eq2 tt =
    let uu =
      FStarC_SMTEncoding_Term.mk_fv ("u", FStarC_SMTEncoding_Term.univ_sort) in
    let aa =
      FStarC_SMTEncoding_Term.mk_fv ("a", FStarC_SMTEncoding_Term.Term_sort) in
    let xx1 =
      FStarC_SMTEncoding_Term.mk_fv ("x", FStarC_SMTEncoding_Term.Term_sort) in
    let yy1 =
      FStarC_SMTEncoding_Term.mk_fv ("y", FStarC_SMTEncoding_Term.Term_sort) in
    let u = FStarC_SMTEncoding_Util.mkFreeV uu in
    let a = FStarC_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStarC_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStarC_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStarC_SMTEncoding_Util.mkApp (eq2, [u; a; x1; y1]) in
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_SMTEncoding_Util.mkEq (x1, y1) in
                (uu___7, valid) in
              FStarC_SMTEncoding_Util.mkIff uu___6 in
            ([[eq2_x_y]], [uu; aa; xx1; yy1], uu___5) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_eq3_interp env eq3 tt =
    let uu =
      FStarC_SMTEncoding_Term.mk_fv ("u", FStarC_SMTEncoding_Term.univ_sort) in
    let aa =
      FStarC_SMTEncoding_Term.mk_fv ("a", FStarC_SMTEncoding_Term.Term_sort) in
    let bb =
      FStarC_SMTEncoding_Term.mk_fv ("b", FStarC_SMTEncoding_Term.Term_sort) in
    let xx1 =
      FStarC_SMTEncoding_Term.mk_fv ("x", FStarC_SMTEncoding_Term.Term_sort) in
    let yy1 =
      FStarC_SMTEncoding_Term.mk_fv ("y", FStarC_SMTEncoding_Term.Term_sort) in
    let u = FStarC_SMTEncoding_Util.mkFreeV uu in
    let a = FStarC_SMTEncoding_Util.mkFreeV aa in
    let b = FStarC_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStarC_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStarC_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStarC_SMTEncoding_Util.mkApp (eq3, [u; a; b; x1; y1]) in
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_SMTEncoding_Util.mkEq (x1, y1) in
                (uu___7, valid) in
              FStarC_SMTEncoding_Util.mkIff uu___6 in
            ([[eq3_x_y]], [uu; aa; bb; xx1; yy1], uu___5) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_imp_interp env imp tt =
    let aa =
      FStarC_SMTEncoding_Term.mk_fv ("a", FStarC_SMTEncoding_Term.Term_sort) in
    let bb =
      FStarC_SMTEncoding_Term.mk_fv ("b", FStarC_SMTEncoding_Term.Term_sort) in
    let a = FStarC_SMTEncoding_Util.mkFreeV aa in
    let b = FStarC_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStarC_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStarC_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStarC_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu___7, valid) in
              FStarC_SMTEncoding_Util.mkIff uu___6 in
            ([[l_imp_a_b]], [aa; bb], uu___5) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_iff_interp env iff tt =
    let aa =
      FStarC_SMTEncoding_Term.mk_fv ("a", FStarC_SMTEncoding_Term.Term_sort) in
    let bb =
      FStarC_SMTEncoding_Term.mk_fv ("b", FStarC_SMTEncoding_Term.Term_sort) in
    let a = FStarC_SMTEncoding_Util.mkFreeV aa in
    let b = FStarC_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStarC_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStarC_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStarC_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu___7, valid) in
              FStarC_SMTEncoding_Util.mkIff uu___6 in
            ([[l_iff_a_b]], [aa; bb], uu___5) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_not_interp env l_not tt =
    let aa =
      FStarC_SMTEncoding_Term.mk_fv ("a", FStarC_SMTEncoding_Term.Term_sort) in
    let a = FStarC_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStarC_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu___ = FStarC_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStarC_SMTEncoding_Util.mkNot uu___ in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 = FStarC_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu___5) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_range_interp env range tt =
    let range_ty = FStarC_SMTEncoding_Util.mkApp (range, []) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_SMTEncoding_Term.mk_Range_const () in
          FStarC_SMTEncoding_Term.mk_HasTypeZ uu___3 range_ty in
        let uu___3 =
          FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.mk_unique
            "typing_range_const" in
        (uu___2, (FStar_Pervasives_Native.Some "Range_const typing"), uu___3) in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_inversion_axiom env inversion tt =
    let uu =
      FStarC_SMTEncoding_Term.mk_fv ("u", FStarC_SMTEncoding_Term.univ_sort) in
    let u = FStarC_SMTEncoding_Util.mkFreeV uu in
    let tt1 =
      FStarC_SMTEncoding_Term.mk_fv ("t", FStarC_SMTEncoding_Term.Term_sort) in
    let t = FStarC_SMTEncoding_Util.mkFreeV tt1 in
    let xx1 =
      FStarC_SMTEncoding_Term.mk_fv ("x", FStarC_SMTEncoding_Term.Term_sort) in
    let x1 = FStarC_SMTEncoding_Util.mkFreeV xx1 in
    let inversion_t = FStarC_SMTEncoding_Util.mkApp (inversion, [u; t]) in
    let valid = FStarC_SMTEncoding_Util.mkApp ("Valid", [inversion_t]) in
    let body =
      let hastypeZ = FStarC_SMTEncoding_Term.mk_HasTypeZ x1 t in
      let hastypeS =
        let uu___ = FStarC_SMTEncoding_Term.n_fuel Prims.int_one in
        FStarC_SMTEncoding_Term.mk_HasTypeFuel uu___ x1 t in
      let uu___ = FStarC_TypeChecker_Env.get_range env in
      let uu___1 =
        let uu___2 = FStarC_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu___2) in
      FStarC_SMTEncoding_Term.mkForall uu___ uu___1 in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 = FStarC_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [uu; tt1], uu___5) in
          FStarC_SMTEncoding_Term.mkForall uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let mk_with_type_axiom env with_type tt =
    let uu =
      FStarC_SMTEncoding_Term.mk_fv ("u", FStarC_SMTEncoding_Term.univ_sort) in
    let u = FStarC_SMTEncoding_Util.mkFreeV uu in
    let tt1 =
      FStarC_SMTEncoding_Term.mk_fv ("t", FStarC_SMTEncoding_Term.Term_sort) in
    let t = FStarC_SMTEncoding_Util.mkFreeV tt1 in
    let ee =
      FStarC_SMTEncoding_Term.mk_fv ("e", FStarC_SMTEncoding_Term.Term_sort) in
    let e = FStarC_SMTEncoding_Util.mkFreeV ee in
    let with_type_t_e = FStarC_SMTEncoding_Util.mkApp (with_type, [u; t; e]) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.get_range env in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_SMTEncoding_Util.mkEq (with_type_t_e, e) in
                let uu___8 =
                  FStarC_SMTEncoding_Term.mk_HasType with_type_t_e t in
                (uu___7, uu___8) in
              FStarC_SMTEncoding_Util.mkAnd uu___6 in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some Prims.int_zero), [uu; tt1; ee],
              uu___5) in
          FStarC_SMTEncoding_Term.mkForall' uu___3 uu___4 in
        (uu___2, (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom") in
      FStarC_SMTEncoding_Util.mkAssume uu___1 in
    [uu___] in
  let prims1 =
    [(FStarC_Parser_Const.unit_lid, mk_unit);
    (FStarC_Parser_Const.bool_lid, mk_bool);
    (FStarC_Parser_Const.int_lid, mk_int);
    (FStarC_Parser_Const.real_lid, mk_real);
    (FStarC_Parser_Const.string_lid, mk_str);
    (FStarC_Parser_Const.true_lid, mk_true_interp);
    (FStarC_Parser_Const.false_lid, mk_false_interp);
    (FStarC_Parser_Const.and_lid, mk_and_interp);
    (FStarC_Parser_Const.or_lid, mk_or_interp);
    (FStarC_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStarC_Parser_Const.imp_lid, mk_imp_interp);
    (FStarC_Parser_Const.iff_lid, mk_iff_interp);
    (FStarC_Parser_Const.not_lid, mk_not_interp);
    (FStarC_Parser_Const.range_lid, mk_range_interp);
    (FStarC_Parser_Const.inversion_lid, mk_inversion_axiom)] in
  fun env t s tt ->
    let uu___ =
      FStarC_Option.find
        (fun uu___1 ->
           match uu___1 with | (l, uu___2) -> FStarC_Ident.lid_equals l t)
        prims1 in
    match uu___ with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some (uu___1, f) -> f env s tt
let forall_univs (rng : FStarC_Range_Type.t)
  (univ_fvs : FStarC_Syntax_Syntax.univ_name Prims.list)
  (body : FStarC_SMTEncoding_Term.term) : FStarC_SMTEncoding_Term.term=
  match univ_fvs with
  | [] -> body
  | us ->
      let univ_vars =
        FStarC_List.map FStarC_SMTEncoding_EncodeTerm.encode_univ_name us in
      let cvars = FStarC_List.map FStar_Pervasives_Native.fst univ_vars in
      let csorts = FStarC_List.map FStarC_SMTEncoding_Term.fv_sort cvars in
      let body1 = FStarC_SMTEncoding_Term.abstr cvars body in
      (match body1 with
       | {
           FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.Quant
             (FStarC_SMTEncoding_Term.Forall, pats, wopt, sorts, body2);
           FStarC_SMTEncoding_Term.freevars = uu___;
           FStarC_SMTEncoding_Term.rng = rng1;_} ->
           FStarC_SMTEncoding_Term.mkForall'' rng1
             (pats, wopt, (FStarC_List.op_At csorts sorts), body2)
       | uu___ ->
           FStarC_SMTEncoding_Term.mkForall'' rng
             ([], FStar_Pervasives_Native.None, csorts, body1))
let encode_smt_lemma (env : FStarC_SMTEncoding_Env.env_t)
  (fv : FStarC_Syntax_Syntax.fv) (t : FStarC_Syntax_Syntax.term) :
  FStarC_SMTEncoding_Term.decls_elt Prims.list=
  let lid = fv.FStarC_Syntax_Syntax.fv_name in
  let t1 = FStarC_Syntax_Util.canon_arrow t in
  let uu___ =
    FStarC_SMTEncoding_EncodeTerm.encode_function_type_as_formula t1 env in
  match uu___ with
  | (form, decls) ->
      let form1 =
        let uu___1 = FStarC_Syntax_Syntax.range_of_fv fv in
        let uu___2 =
          let uu___3 = FStarC_Syntax_Free.univnames t1 in
          FStarC_Class_Setlike.elems ()
            (Obj.magic
               (FStarC_FlatSet.setlike_flat_set
                  FStarC_Syntax_Syntax.ord_ident)) (Obj.magic uu___3) in
        forall_univs uu___1 uu___2 form in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = FStarC_Ident.string_of_lid lid in
                  Prims.strcat "Lemma: " uu___7 in
                FStar_Pervasives_Native.Some uu___6 in
              let uu___6 =
                let uu___7 = FStarC_Ident.string_of_lid lid in
                Prims.strcat "lemma_" uu___7 in
              (form1, uu___5, uu___6) in
            FStarC_SMTEncoding_Util.mkAssume uu___4 in
          [uu___3] in
        FStarC_SMTEncoding_Term.mk_decls_trivial uu___2 in
      FStarC_List.op_At decls uu___1
let close_universes (rng : FStarC_Range_Type.t)
  (univ_fvs : FStarC_SMTEncoding_Term.fvs)
  (pat : FStarC_SMTEncoding_Term.pat) (body : FStarC_SMTEncoding_Term.term) :
  FStarC_SMTEncoding_Term.term=
  FStarC_SMTEncoding_Term.mkForall rng ([[pat]], univ_fvs, body)
let encode_free_var (uninterpreted : Prims.bool)
  (env : FStarC_SMTEncoding_Env.env_t) (fv : FStarC_Syntax_Syntax.fv)
  (us : FStarC_Syntax_Syntax.univ_name Prims.list)
  (tt : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  (t_norm : FStarC_Syntax_Syntax.term)
  (quals : FStarC_Syntax_Syntax.qualifier Prims.list) :
  (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.env_t)=
  let lid = fv.FStarC_Syntax_Syntax.fv_name in
  let uu___ =
    let uu___1 =
      FStarC_List.map FStarC_SMTEncoding_EncodeTerm.encode_univ_name us in
    FStarC_List.unzip uu___1 in
  match uu___ with
  | (univ_fvs, univs) ->
      let univ_sorts =
        FStarC_List.map (fun uu___1 -> FStarC_SMTEncoding_Term.univ_sort)
          univs in
      let uu___1 =
        ((let uu___2 =
            (FStarC_Syntax_Util.is_pure_or_ghost_function t_norm) ||
              (FStarC_SMTEncoding_Util.is_smt_reifiable_function
                 env.FStarC_SMTEncoding_Env.tcenv t_norm) in
          Prims.op_Negation uu___2) || (FStarC_Syntax_Util.is_lemma t_norm))
          || uninterpreted in
      if uu___1
      then
        let arg_sorts =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Subst.compress t_norm in
            uu___3.FStarC_Syntax_Syntax.n in
          match uu___2 with
          | FStarC_Syntax_Syntax.Tm_arrow
              { FStarC_Syntax_Syntax.bs1 = binders;
                FStarC_Syntax_Syntax.comp = uu___3;_}
              ->
              FStarC_List.map
                (fun uu___4 -> FStarC_SMTEncoding_Term.Term_sort) binders
          | uu___3 -> [] in
        let arity = FStarC_List.length arg_sorts in
        let univ_arity = FStarC_List.length us in
        let uu___2 =
          FStarC_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
            arity univ_arity in
        (match uu___2 with
         | (vname, vtok, env1) ->
             let univ_sorts1 =
               FStarC_List.map
                 (fun uu___3 -> FStarC_SMTEncoding_Term.univ_sort) us in
             let d =
               FStarC_SMTEncoding_Term.DeclFun
                 (vname, (FStarC_List.op_At univ_sorts1 arg_sorts),
                   FStarC_SMTEncoding_Term.Term_sort,
                   (FStar_Pervasives_Native.Some
                      "Uninterpreted function symbol for impure function")) in
             let dd =
               FStarC_SMTEncoding_Term.DeclFun
                 (vtok, univ_sorts1, FStarC_SMTEncoding_Term.Term_sort,
                   (FStar_Pervasives_Native.Some
                      "Uninterpreted name for impure function")) in
             let uu___3 = FStarC_SMTEncoding_Term.mk_decls_trivial [d; dd] in
             (uu___3, env1))
      else
        (let uu___3 = prims.is lid in
         if uu___3
         then
           (if (FStarC_List.length us) <> Prims.int_zero
            then
              failwith
                "Impossible: unexpected universe-polymorphic primitive function"
            else ();
            (let vname =
               FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.new_fvar
                 lid in
             let uu___5 = prims.mk lid vname in
             match uu___5 with
             | (tok, arity, definition) ->
                 let env1 =
                   FStarC_SMTEncoding_Env.push_free_var env lid arity
                     Prims.int_zero vname (FStar_Pervasives_Native.Some tok) in
                 let uu___6 =
                   FStarC_SMTEncoding_Term.mk_decls_trivial definition in
                 (uu___6, env1)))
         else
           (let encode_non_total_function_typ =
              let uu___5 = FStarC_Ident.nsstr lid in uu___5 <> "Prims" in
            let uu___5 =
              let uu___6 =
                FStarC_SMTEncoding_EncodeTerm.curried_arrow_formals_comp
                  t_norm in
              match uu___6 with
              | (args, comp) ->
                  let tcenv_comp =
                    FStarC_TypeChecker_Env.push_binders
                      env.FStarC_SMTEncoding_Env.tcenv args in
                  let comp1 =
                    let uu___7 =
                      FStarC_SMTEncoding_Util.is_smt_reifiable_comp
                        env.FStarC_SMTEncoding_Env.tcenv comp in
                    if uu___7
                    then
                      let uu___8 =
                        FStarC_TypeChecker_Env.reify_comp
                          {
                            FStarC_TypeChecker_Env.solver =
                              (tcenv_comp.FStarC_TypeChecker_Env.solver);
                            FStarC_TypeChecker_Env.range =
                              (tcenv_comp.FStarC_TypeChecker_Env.range);
                            FStarC_TypeChecker_Env.curmodule =
                              (tcenv_comp.FStarC_TypeChecker_Env.curmodule);
                            FStarC_TypeChecker_Env.gamma =
                              (tcenv_comp.FStarC_TypeChecker_Env.gamma);
                            FStarC_TypeChecker_Env.gamma_sig =
                              (tcenv_comp.FStarC_TypeChecker_Env.gamma_sig);
                            FStarC_TypeChecker_Env.gamma_cache =
                              (tcenv_comp.FStarC_TypeChecker_Env.gamma_cache);
                            FStarC_TypeChecker_Env.modules =
                              (tcenv_comp.FStarC_TypeChecker_Env.modules);
                            FStarC_TypeChecker_Env.expected_typ =
                              (tcenv_comp.FStarC_TypeChecker_Env.expected_typ);
                            FStarC_TypeChecker_Env.sigtab =
                              (tcenv_comp.FStarC_TypeChecker_Env.sigtab);
                            FStarC_TypeChecker_Env.attrtab =
                              (tcenv_comp.FStarC_TypeChecker_Env.attrtab);
                            FStarC_TypeChecker_Env.instantiate_imp =
                              (tcenv_comp.FStarC_TypeChecker_Env.instantiate_imp);
                            FStarC_TypeChecker_Env.effects =
                              (tcenv_comp.FStarC_TypeChecker_Env.effects);
                            FStarC_TypeChecker_Env.generalize =
                              (tcenv_comp.FStarC_TypeChecker_Env.generalize);
                            FStarC_TypeChecker_Env.letrecs =
                              (tcenv_comp.FStarC_TypeChecker_Env.letrecs);
                            FStarC_TypeChecker_Env.top_level =
                              (tcenv_comp.FStarC_TypeChecker_Env.top_level);
                            FStarC_TypeChecker_Env.check_uvars =
                              (tcenv_comp.FStarC_TypeChecker_Env.check_uvars);
                            FStarC_TypeChecker_Env.use_eq_strict =
                              (tcenv_comp.FStarC_TypeChecker_Env.use_eq_strict);
                            FStarC_TypeChecker_Env.is_iface =
                              (tcenv_comp.FStarC_TypeChecker_Env.is_iface);
                            FStarC_TypeChecker_Env.admit = true;
                            FStarC_TypeChecker_Env.phase1 =
                              (tcenv_comp.FStarC_TypeChecker_Env.phase1);
                            FStarC_TypeChecker_Env.failhard =
                              (tcenv_comp.FStarC_TypeChecker_Env.failhard);
                            FStarC_TypeChecker_Env.flychecking =
                              (tcenv_comp.FStarC_TypeChecker_Env.flychecking);
                            FStarC_TypeChecker_Env.uvar_subtyping =
                              (tcenv_comp.FStarC_TypeChecker_Env.uvar_subtyping);
                            FStarC_TypeChecker_Env.intactics =
                              (tcenv_comp.FStarC_TypeChecker_Env.intactics);
                            FStarC_TypeChecker_Env.nocoerce =
                              (tcenv_comp.FStarC_TypeChecker_Env.nocoerce);
                            FStarC_TypeChecker_Env.tc_term =
                              (tcenv_comp.FStarC_TypeChecker_Env.tc_term);
                            FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
                              (tcenv_comp.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                            FStarC_TypeChecker_Env.universe_of =
                              (tcenv_comp.FStarC_TypeChecker_Env.universe_of);
                            FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                              =
                              (tcenv_comp.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                            FStarC_TypeChecker_Env.teq_nosmt_force =
                              (tcenv_comp.FStarC_TypeChecker_Env.teq_nosmt_force);
                            FStarC_TypeChecker_Env.subtype_nosmt_force =
                              (tcenv_comp.FStarC_TypeChecker_Env.subtype_nosmt_force);
                            FStarC_TypeChecker_Env.qtbl_name_and_index =
                              (tcenv_comp.FStarC_TypeChecker_Env.qtbl_name_and_index);
                            FStarC_TypeChecker_Env.normalized_eff_names =
                              (tcenv_comp.FStarC_TypeChecker_Env.normalized_eff_names);
                            FStarC_TypeChecker_Env.fv_delta_depths =
                              (tcenv_comp.FStarC_TypeChecker_Env.fv_delta_depths);
                            FStarC_TypeChecker_Env.proof_ns =
                              (tcenv_comp.FStarC_TypeChecker_Env.proof_ns);
                            FStarC_TypeChecker_Env.synth_hook =
                              (tcenv_comp.FStarC_TypeChecker_Env.synth_hook);
                            FStarC_TypeChecker_Env.try_solve_implicits_hook =
                              (tcenv_comp.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                            FStarC_TypeChecker_Env.splice =
                              (tcenv_comp.FStarC_TypeChecker_Env.splice);
                            FStarC_TypeChecker_Env.mpreprocess =
                              (tcenv_comp.FStarC_TypeChecker_Env.mpreprocess);
                            FStarC_TypeChecker_Env.postprocess =
                              (tcenv_comp.FStarC_TypeChecker_Env.postprocess);
                            FStarC_TypeChecker_Env.identifier_info =
                              (tcenv_comp.FStarC_TypeChecker_Env.identifier_info);
                            FStarC_TypeChecker_Env.tc_hooks =
                              (tcenv_comp.FStarC_TypeChecker_Env.tc_hooks);
                            FStarC_TypeChecker_Env.dsenv =
                              (tcenv_comp.FStarC_TypeChecker_Env.dsenv);
                            FStarC_TypeChecker_Env.nbe =
                              (tcenv_comp.FStarC_TypeChecker_Env.nbe);
                            FStarC_TypeChecker_Env.strict_args_tab =
                              (tcenv_comp.FStarC_TypeChecker_Env.strict_args_tab);
                            FStarC_TypeChecker_Env.erasable_types_tab =
                              (tcenv_comp.FStarC_TypeChecker_Env.erasable_types_tab);
                            FStarC_TypeChecker_Env.enable_defer_to_tac =
                              (tcenv_comp.FStarC_TypeChecker_Env.enable_defer_to_tac);
                            FStarC_TypeChecker_Env.unif_allow_ref_guards =
                              (tcenv_comp.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                            FStarC_TypeChecker_Env.erase_erasable_args =
                              (tcenv_comp.FStarC_TypeChecker_Env.erase_erasable_args);
                            FStarC_TypeChecker_Env.core_check =
                              (tcenv_comp.FStarC_TypeChecker_Env.core_check);
                            FStarC_TypeChecker_Env.missing_decl =
                              (tcenv_comp.FStarC_TypeChecker_Env.missing_decl)
                          } comp FStarC_Syntax_Syntax.U_unknown in
                      FStarC_Syntax_Syntax.mk_Total uu___8
                    else comp in
                  if encode_non_total_function_typ
                  then
                    let uu___7 =
                      FStarC_TypeChecker_Util.pure_or_ghost_pre_and_post
                        tcenv_comp comp1 in
                    (args, uu___7)
                  else
                    (let uu___8 =
                       let uu___9 = FStarC_Syntax_Util.comp_result comp1 in
                       (FStar_Pervasives_Native.None, uu___9) in
                     (args, uu___8)) in
            match uu___5 with
            | (formals, (pre_opt, res_t)) ->
                let mk_disc_proj_axioms guard encoded_res_t vapp vars =
                  FStarC_List.collect
                    (fun uu___6 ->
                       match uu___6 with
                       | FStarC_Syntax_Syntax.Discriminator d ->
                           let uu___7 = FStarC_Util.prefix vars in
                           (match uu___7 with
                            | (uu___8, xxv) ->
                                let xx =
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        FStarC_SMTEncoding_Term.fv_name xxv in
                                      (uu___11,
                                        FStarC_SMTEncoding_Term.Term_sort) in
                                    FStarC_SMTEncoding_Term.mk_fv uu___10 in
                                  FStarC_SMTEncoding_Util.mkFreeV uu___9 in
                                let uu___9 =
                                  let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        FStarC_Syntax_Syntax.range_of_fv fv in
                                      let uu___13 =
                                        let uu___14 =
                                          let uu___15 =
                                            let uu___16 =
                                              let uu___17 =
                                                let uu___18 =
                                                  let uu___19 =
                                                    FStarC_Ident.string_of_lid
                                                      d in
                                                  FStarC_SMTEncoding_Env.escape
                                                    uu___19 in
                                                FStarC_SMTEncoding_Term.mk_tester
                                                  uu___18 xx in
                                              FStarC_SMTEncoding_Term.boxBool
                                                uu___17 in
                                            (vapp, uu___16) in
                                          FStarC_SMTEncoding_Util.mkEq
                                            uu___15 in
                                        ([[vapp]],
                                          (FStarC_List.op_At univ_fvs vars),
                                          uu___14) in
                                      FStarC_SMTEncoding_Term.mkForall
                                        uu___12 uu___13 in
                                    let uu___12 =
                                      let uu___13 =
                                        let uu___14 =
                                          FStarC_Ident.string_of_lid d in
                                        FStarC_SMTEncoding_Env.escape uu___14 in
                                      Prims.strcat "disc_equation_" uu___13 in
                                    (uu___11,
                                      (FStar_Pervasives_Native.Some
                                         "Discriminator equation"), uu___12) in
                                  FStarC_SMTEncoding_Util.mkAssume uu___10 in
                                [uu___9])
                       | FStarC_Syntax_Syntax.Projector (d, f) ->
                           let uu___7 = FStarC_Util.prefix vars in
                           (match uu___7 with
                            | (uu___8, xxv) ->
                                let xx =
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        FStarC_SMTEncoding_Term.fv_name xxv in
                                      (uu___11,
                                        FStarC_SMTEncoding_Term.Term_sort) in
                                    FStarC_SMTEncoding_Term.mk_fv uu___10 in
                                  FStarC_SMTEncoding_Util.mkFreeV uu___9 in
                                let f1 =
                                  {
                                    FStarC_Syntax_Syntax.ppname = f;
                                    FStarC_Syntax_Syntax.index =
                                      Prims.int_zero;
                                    FStarC_Syntax_Syntax.sort =
                                      FStarC_Syntax_Syntax.tun
                                  } in
                                let tp_name =
                                  FStarC_SMTEncoding_Env.mk_term_projector_name
                                    d f1 in
                                let prim_app =
                                  FStarC_SMTEncoding_Util.mkApp
                                    (tp_name, [xx]) in
                                let uu___9 =
                                  let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        FStarC_Syntax_Syntax.range_of_fv fv in
                                      let uu___13 =
                                        let uu___14 =
                                          FStarC_SMTEncoding_Util.mkEq
                                            (vapp, prim_app) in
                                        ([[vapp]],
                                          (FStarC_List.op_At univ_fvs vars),
                                          uu___14) in
                                      FStarC_SMTEncoding_Term.mkForall
                                        uu___12 uu___13 in
                                    (uu___11,
                                      (FStar_Pervasives_Native.Some
                                         "Projector equation"),
                                      (Prims.strcat "proj_equation_" tp_name)) in
                                  FStarC_SMTEncoding_Util.mkAssume uu___10 in
                                [uu___9])
                       | uu___7 -> []) quals in
                let uu___6 =
                  FStarC_SMTEncoding_EncodeTerm.encode_binders
                    FStar_Pervasives_Native.None formals env in
                (match uu___6 with
                 | (vars, guards, env', decls1, uu___7) ->
                     let uu___8 =
                       match pre_opt with
                       | FStar_Pervasives_Native.None ->
                           let uu___9 =
                             FStarC_SMTEncoding_Util.mk_and_l guards in
                           (uu___9, decls1)
                       | FStar_Pervasives_Native.Some p ->
                           let uu___9 =
                             FStarC_SMTEncoding_EncodeTerm.encode_formula p
                               env' in
                           (match uu___9 with
                            | (g, ds) ->
                                let uu___10 =
                                  FStarC_SMTEncoding_Util.mk_and_l (g ::
                                    guards) in
                                (uu___10, (FStarC_List.op_At decls1 ds))) in
                     (match uu___8 with
                      | (guard, decls11) ->
                          let dummy_var =
                            FStarC_SMTEncoding_Term.mk_fv
                              ("@dummy", FStarC_SMTEncoding_Term.dummy_sort) in
                          let dummy_tm =
                            FStarC_SMTEncoding_Term.mkFreeV dummy_var
                              FStarC_Range_Type.dummyRange in
                          let should_thunk uu___9 =
                            let is_type t =
                              let uu___10 =
                                let uu___11 = FStarC_Syntax_Subst.compress t in
                                uu___11.FStarC_Syntax_Syntax.n in
                              match uu___10 with
                              | FStarC_Syntax_Syntax.Tm_type uu___11 -> true
                              | uu___11 -> false in
                            let is_squash t =
                              let uu___10 =
                                FStarC_Syntax_Util.head_and_args t in
                              match uu___10 with
                              | (head, uu___11) ->
                                  let uu___12 =
                                    let uu___13 =
                                      FStarC_Syntax_Util.un_uinst head in
                                    uu___13.FStarC_Syntax_Syntax.n in
                                  (match uu___12 with
                                   | FStarC_Syntax_Syntax.Tm_fvar fv1 ->
                                       FStarC_Syntax_Syntax.fv_eq_lid fv1
                                         FStarC_Parser_Const.squash_lid
                                   | FStarC_Syntax_Syntax.Tm_refine
                                       {
                                         FStarC_Syntax_Syntax.b =
                                           {
                                             FStarC_Syntax_Syntax.ppname =
                                               uu___13;
                                             FStarC_Syntax_Syntax.index =
                                               uu___14;
                                             FStarC_Syntax_Syntax.sort =
                                               {
                                                 FStarC_Syntax_Syntax.n =
                                                   FStarC_Syntax_Syntax.Tm_fvar
                                                   fv1;
                                                 FStarC_Syntax_Syntax.pos =
                                                   uu___15;
                                                 FStarC_Syntax_Syntax.vars =
                                                   uu___16;
                                                 FStarC_Syntax_Syntax.hash_code
                                                   = uu___17;_};_};
                                         FStarC_Syntax_Syntax.phi = uu___18;_}
                                       ->
                                       FStarC_Syntax_Syntax.fv_eq_lid fv1
                                         FStarC_Parser_Const.unit_lid
                                   | uu___13 -> false) in
                            ((((let uu___10 = FStarC_Ident.nsstr lid in
                                uu___10 <> "Prims") &&
                                 ((FStarC_List.length us) = Prims.int_zero))
                                &&
                                (Prims.op_Negation
                                   (FStarC_List.contains
                                      FStarC_Syntax_Syntax.Logic quals)))
                               &&
                               (let uu___10 = is_squash t_norm in
                                Prims.op_Negation uu___10))
                              &&
                              (let uu___10 = is_type t_norm in
                               Prims.op_Negation uu___10) in
                          let uu___9 =
                            match vars with
                            | [] when should_thunk () -> (true, [dummy_var])
                            | uu___10 -> (false, vars) in
                          (match uu___9 with
                           | (thunked, vars1) ->
                               let arity = FStarC_List.length formals in
                               let univ_arity = FStarC_List.length univs in
                               let uu___10 =
                                 FStarC_SMTEncoding_Env.new_term_constant_and_tok_from_lid_maybe_thunked
                                   env lid arity univ_arity thunked in
                               (match uu___10 with
                                | (vname, vtok_opt, env1) ->
                                    let get_vtok uu___11 =
                                      FStarC_Option.must vtok_opt in
                                    let vtok_tm =
                                      match formals with
                                      | [] when thunked ->
                                          FStarC_SMTEncoding_Util.mkApp
                                            (vname, [dummy_tm])
                                      | [] when Prims.op_Negation thunked ->
                                          FStarC_SMTEncoding_Util.mkApp
                                            (vname, univs)
                                      | uu___11 ->
                                          let uu___12 =
                                            let uu___13 = get_vtok () in
                                            (uu___13, univs) in
                                          FStarC_SMTEncoding_Util.mkApp
                                            uu___12 in
                                    let vtok_app =
                                      FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                        vtok_tm vars1 in
                                    let vapp =
                                      let uu___11 =
                                        let uu___12 =
                                          let uu___13 =
                                            FStarC_List.map
                                              FStarC_SMTEncoding_Util.mkFreeV
                                              vars1 in
                                          FStarC_List.op_At univs uu___13 in
                                        (vname, uu___12) in
                                      FStarC_SMTEncoding_Util.mkApp uu___11 in
                                    let uu___11 =
                                      let vname_decl =
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              FStarC_List.map
                                                FStarC_SMTEncoding_Term.fv_sort
                                                vars1 in
                                            FStarC_List.op_At univ_sorts
                                              uu___14 in
                                          (vname, uu___13,
                                            FStarC_SMTEncoding_Term.Term_sort,
                                            FStar_Pervasives_Native.None) in
                                        FStarC_SMTEncoding_Term.DeclFun
                                          uu___12 in
                                      let uu___12 =
                                        let env2 =
                                          {
                                            FStarC_SMTEncoding_Env.bvar_bindings
                                              =
                                              (env1.FStarC_SMTEncoding_Env.bvar_bindings);
                                            FStarC_SMTEncoding_Env.fvar_bindings
                                              =
                                              (env1.FStarC_SMTEncoding_Env.fvar_bindings);
                                            FStarC_SMTEncoding_Env.depth =
                                              (env1.FStarC_SMTEncoding_Env.depth);
                                            FStarC_SMTEncoding_Env.tcenv =
                                              (env1.FStarC_SMTEncoding_Env.tcenv);
                                            FStarC_SMTEncoding_Env.warn =
                                              (env1.FStarC_SMTEncoding_Env.warn);
                                            FStarC_SMTEncoding_Env.nolabels =
                                              (env1.FStarC_SMTEncoding_Env.nolabels);
                                            FStarC_SMTEncoding_Env.use_zfuel_name
                                              =
                                              (env1.FStarC_SMTEncoding_Env.use_zfuel_name);
                                            FStarC_SMTEncoding_Env.encode_non_total_function_typ
                                              = encode_non_total_function_typ;
                                            FStarC_SMTEncoding_Env.current_module_name
                                              =
                                              (env1.FStarC_SMTEncoding_Env.current_module_name);
                                            FStarC_SMTEncoding_Env.encoding_quantifier
                                              =
                                              (env1.FStarC_SMTEncoding_Env.encoding_quantifier);
                                            FStarC_SMTEncoding_Env.global_cache
                                              =
                                              (env1.FStarC_SMTEncoding_Env.global_cache)
                                          } in
                                        let uu___13 =
                                          let uu___14 =
                                            FStarC_SMTEncoding_EncodeTerm.head_normal
                                              env2 tt in
                                          Prims.op_Negation uu___14 in
                                        if uu___13
                                        then
                                          FStarC_SMTEncoding_EncodeTerm.encode_term_pred
                                            FStar_Pervasives_Native.None tt
                                            env2 vtok_tm
                                        else
                                          FStarC_SMTEncoding_EncodeTerm.encode_term_pred
                                            FStar_Pervasives_Native.None
                                            t_norm env2 vtok_tm in
                                      match uu___12 with
                                      | (tok_typing, decls2) ->
                                          let tok_typing1 =
                                            let uu___13 =
                                              FStarC_Syntax_Syntax.range_of_fv
                                                fv in
                                            close_universes uu___13 univ_fvs
                                              vtok_tm tok_typing in
                                          let uu___13 =
                                            match vars1 with
                                            | [] ->
                                                let tok_typing2 =
                                                  FStarC_SMTEncoding_Util.mkAssume
                                                    (tok_typing1,
                                                      (FStar_Pervasives_Native.Some
                                                         "function token typing"),
                                                      (Prims.strcat
                                                         "function_token_typing_"
                                                         vname)) in
                                                let uu___14 =
                                                  let uu___15 =
                                                    FStarC_SMTEncoding_Term.mk_decls_trivial
                                                      [tok_typing2] in
                                                  FStarC_List.op_At decls2
                                                    uu___15 in
                                                let uu___15 =
                                                  let uu___16 =
                                                    let uu___17 =
                                                      FStarC_SMTEncoding_Util.mkApp
                                                        (vname, []) in
                                                    FStar_Pervasives_Native.Some
                                                      uu___17 in
                                                  FStarC_SMTEncoding_Env.push_free_var
                                                    env1 lid arity univ_arity
                                                    vname uu___16 in
                                                (uu___14, uu___15)
                                            | uu___14 when thunked ->
                                                (decls2, env1)
                                            | uu___14 ->
                                                let vtok = get_vtok () in
                                                let vtok_decl =
                                                  FStarC_SMTEncoding_Term.DeclFun
                                                    (vtok, univ_sorts,
                                                      FStarC_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let name_tok_corr_formula pat
                                                  =
                                                  match univ_fvs with
                                                  | [] ->
                                                      let uu___15 =
                                                        FStarC_Syntax_Syntax.range_of_fv
                                                          fv in
                                                      let uu___16 =
                                                        let uu___17 =
                                                          FStarC_SMTEncoding_Util.mkEq
                                                            (vtok_app, vapp) in
                                                        ([[pat]], vars1,
                                                          uu___17) in
                                                      FStarC_SMTEncoding_Term.mkForall
                                                        uu___15 uu___16
                                                  | uu___15 ->
                                                      let inner_quant =
                                                        let uu___16 =
                                                          FStarC_Syntax_Syntax.range_of_fv
                                                            fv in
                                                        let uu___17 =
                                                          let uu___18 =
                                                            FStarC_SMTEncoding_Util.mkEq
                                                              (vtok_app,
                                                                vapp) in
                                                          ([[vtok_app];
                                                           [vapp]], vars1,
                                                            uu___18) in
                                                        FStarC_SMTEncoding_Term.mkForall
                                                          uu___16 uu___17 in
                                                      let uu___16 =
                                                        FStarC_Syntax_Syntax.range_of_fv
                                                          fv in
                                                      FStarC_SMTEncoding_Term.mkForall
                                                        uu___16
                                                        ([[vtok_tm]],
                                                          univ_fvs,
                                                          inner_quant) in
                                                let name_tok_corr =
                                                  let uu___15 =
                                                    let uu___16 =
                                                      name_tok_corr_formula
                                                        vtok_app in
                                                    (uu___16,
                                                      (FStar_Pervasives_Native.Some
                                                         "Name-token correspondence"),
                                                      (Prims.strcat
                                                         "token_correspondence_"
                                                         vname)) in
                                                  FStarC_SMTEncoding_Util.mkAssume
                                                    uu___15 in
                                                let tok_typing2 =
                                                  let guarded_tok_typing =
                                                    match univ_fvs with
                                                    | uu___15::uu___16 ->
                                                        tok_typing1
                                                    | uu___15 ->
                                                        let ff =
                                                          FStarC_SMTEncoding_Term.mk_fv
                                                            ("ty",
                                                              FStarC_SMTEncoding_Term.Term_sort) in
                                                        let f =
                                                          FStarC_SMTEncoding_Util.mkFreeV
                                                            ff in
                                                        let vtok_app_r =
                                                          let uu___16 =
                                                            let uu___17 =
                                                              FStarC_SMTEncoding_Term.mk_fv
                                                                (vtok,
                                                                  FStarC_SMTEncoding_Term.Term_sort) in
                                                            [uu___17] in
                                                          FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                                            f uu___16 in
                                                        let uu___16 =
                                                          FStarC_Syntax_Syntax.range_of_fv
                                                            fv in
                                                        let uu___17 =
                                                          let uu___18 =
                                                            let uu___19 =
                                                              let uu___20 =
                                                                FStarC_SMTEncoding_Term.mk_NoHoist
                                                                  f
                                                                  tok_typing1 in
                                                              let uu___21 =
                                                                name_tok_corr_formula
                                                                  vapp in
                                                              (uu___20,
                                                                uu___21) in
                                                            FStarC_SMTEncoding_Util.mkAnd
                                                              uu___19 in
                                                          ([[vtok_app_r]],
                                                            [ff], uu___18) in
                                                        FStarC_SMTEncoding_Term.mkForall
                                                          uu___16 uu___17 in
                                                  FStarC_SMTEncoding_Util.mkAssume
                                                    (guarded_tok_typing,
                                                      (FStar_Pervasives_Native.Some
                                                         "function token typing"),
                                                      (Prims.strcat
                                                         "function_token_typing_"
                                                         vname)) in
                                                let uu___15 =
                                                  let uu___16 =
                                                    FStarC_SMTEncoding_Term.mk_decls_trivial
                                                      [vtok_decl;
                                                      name_tok_corr;
                                                      tok_typing2] in
                                                  FStarC_List.op_At decls2
                                                    uu___16 in
                                                (uu___15, env1) in
                                          (match uu___13 with
                                           | (tok_decl, env2) ->
                                               let uu___14 =
                                                 let uu___15 =
                                                   FStarC_SMTEncoding_Term.mk_decls_trivial
                                                     [vname_decl] in
                                                 FStarC_List.op_At uu___15
                                                   tok_decl in
                                               (uu___14, env2)) in
                                    (match uu___11 with
                                     | (decls2, env2) ->
                                         let uu___12 =
                                           let res_t1 =
                                             FStarC_Syntax_Subst.compress
                                               res_t in
                                           let uu___13 =
                                             FStarC_SMTEncoding_EncodeTerm.encode_term
                                               res_t1 env' in
                                           match uu___13 with
                                           | (encoded_res_t, decls) ->
                                               let uu___14 =
                                                 FStarC_SMTEncoding_Term.mk_HasType
                                                   vapp encoded_res_t in
                                               (encoded_res_t, uu___14,
                                                 decls) in
                                         (match uu___12 with
                                          | (encoded_res_t, ty_pred, decls3)
                                              ->
                                              let typingAx =
                                                let uu___13 =
                                                  let uu___14 =
                                                    let uu___15 =
                                                      FStarC_Syntax_Syntax.range_of_fv
                                                        fv in
                                                    let uu___16 =
                                                      let uu___17 =
                                                        FStarC_SMTEncoding_Util.mkImp
                                                          (guard, ty_pred) in
                                                      ([[vapp]],
                                                        (FStarC_List.op_At
                                                           univ_fvs vars1),
                                                        uu___17) in
                                                    FStarC_SMTEncoding_Term.mkForall
                                                      uu___15 uu___16 in
                                                  (uu___14,
                                                    (FStar_Pervasives_Native.Some
                                                       "free var typing"),
                                                    (Prims.strcat "typing_"
                                                       vname)) in
                                                FStarC_SMTEncoding_Util.mkAssume
                                                  uu___13 in
                                              let freshness =
                                                if
                                                  FStarC_List.contains
                                                    FStarC_Syntax_Syntax.New
                                                    quals
                                                then
                                                  let uu___13 =
                                                    let uu___14 =
                                                      FStarC_Syntax_Syntax.range_of_fv
                                                        fv in
                                                    let uu___15 =
                                                      let uu___16 =
                                                        let uu___17 =
                                                          FStarC_List.map
                                                            FStarC_SMTEncoding_Term.fv_sort
                                                            vars1 in
                                                        FStarC_List.op_At
                                                          univ_sorts uu___17 in
                                                      let uu___17 =
                                                        FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.next_id
                                                          () in
                                                      (vname, uu___16,
                                                        FStarC_SMTEncoding_Term.Term_sort,
                                                        uu___17) in
                                                    FStarC_SMTEncoding_Term.fresh_constructor
                                                      uu___14 uu___15 in
                                                  let uu___14 =
                                                    let uu___15 =
                                                      let uu___16 =
                                                        FStarC_Syntax_Syntax.range_of_fv
                                                          fv in
                                                      pretype_axiom false
                                                        uu___16 env2 vapp
                                                        (FStarC_List.op_At
                                                           univ_fvs vars1) in
                                                    [uu___15] in
                                                  uu___13 :: uu___14
                                                else [] in
                                              let g =
                                                let uu___13 =
                                                  let uu___14 =
                                                    let uu___15 =
                                                      let uu___16 =
                                                        let uu___17 =
                                                          let uu___18 =
                                                            mk_disc_proj_axioms
                                                              guard
                                                              encoded_res_t
                                                              vapp vars1 in
                                                          typingAx :: uu___18 in
                                                        FStarC_List.op_At
                                                          freshness uu___17 in
                                                      FStarC_SMTEncoding_Term.mk_decls_trivial
                                                        uu___16 in
                                                    FStarC_List.op_At decls3
                                                      uu___15 in
                                                  FStarC_List.op_At decls2
                                                    uu___14 in
                                                FStarC_List.op_At decls11
                                                  uu___13 in
                                              (g, env2)))))))))
let declare_top_level_let (env : FStarC_SMTEncoding_Env.env_t)
  (x : FStarC_Syntax_Syntax.fv)
  (us : FStarC_Syntax_Syntax.univ_name Prims.list)
  (t : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  (t_norm : FStarC_Syntax_Syntax.term) :
  (FStarC_SMTEncoding_Env.fvar_binding * FStarC_SMTEncoding_Term.decls_t *
    FStarC_SMTEncoding_Env.env_t)=
  let uu___ =
    FStarC_SMTEncoding_Env.lookup_fvar_binding env
      x.FStarC_Syntax_Syntax.fv_name in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let uu___1 = encode_free_var false env x us t t_norm [] in
      (match uu___1 with
       | (decls, env1) ->
           let fvb =
             FStarC_SMTEncoding_Env.lookup_lid env1
               x.FStarC_Syntax_Syntax.fv_name in
           (fvb, decls, env1))
  | FStar_Pervasives_Native.Some fvb -> (fvb, [], env)
let encode_top_level_val (uninterpreted : Prims.bool)
  (env : FStarC_SMTEncoding_Env.env_t)
  (us : FStarC_Syntax_Syntax.univ_name Prims.list)
  (fv : FStarC_Syntax_Syntax.fv)
  (t : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  (quals : FStarC_Syntax_Syntax.qualifier Prims.list) :
  (FStarC_SMTEncoding_Term.decls_elt Prims.list *
    FStarC_SMTEncoding_Env.env_t)=
  let tt =
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Syntax_Syntax.lid_of_fv fv in
        FStarC_Ident.nsstr uu___2 in
      uu___1 = "FStar.Ghost" in
    if uu___
    then
      norm_with_steps
        [FStarC_TypeChecker_Env.Eager_unfolding;
        FStarC_TypeChecker_Env.AllowUnboundUniverses;
        FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta]
        env.FStarC_SMTEncoding_Env.tcenv t
    else norm_before_encoding env t in
  (let uu___1 = FStarC_Effect.op_Bang dbg_SMTEncoding in
   if uu___1
   then
     let uu___2 = FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_fv fv in
     let uu___3 =
       FStarC_Class_Show.show
         (FStarC_Class_Show.show_list FStarC_Ident.showable_ident) us in
     let uu___4 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
     let uu___5 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term tt in
     FStarC_Format.print4
       "Encoding top-level val %s %s : %s\nNormalized to is %s\n" uu___2
       uu___3 uu___4 uu___5
   else ());
  (let uu___1 = encode_free_var uninterpreted env fv us t tt quals in
   match uu___1 with
   | (decls, env1) ->
       let uu___2 = FStarC_Syntax_Util.is_smt_lemma t in
       if uu___2
       then
         let uu___3 =
           let uu___4 = encode_smt_lemma env1 fv tt in
           FStarC_List.op_At decls uu___4 in
         (uu___3, env1)
       else (decls, env1))
let encode_top_level_vals (env : FStarC_SMTEncoding_Env.env_t)
  (bindings : FStarC_Syntax_Syntax.letbinding Prims.list)
  (quals : FStarC_Syntax_Syntax.qualifier Prims.list) :
  (FStarC_SMTEncoding_Term.decls_elt Prims.list *
    FStarC_SMTEncoding_Env.env_t)=
  let uu___ =
    FStarC_List.fold_left
      (fun uu___1 lb ->
         match uu___1 with
         | (decls, env1) ->
             let uu___2 =
               FStarC_TypeChecker_Env.open_universes_in
                 env1.FStarC_SMTEncoding_Env.tcenv
                 lb.FStarC_Syntax_Syntax.lbunivs
                 [lb.FStarC_Syntax_Syntax.lbtyp] in
             (match uu___2 with
              | (env', us, t::[]) ->
                  let env'1 =
                    {
                      FStarC_SMTEncoding_Env.bvar_bindings =
                        (env1.FStarC_SMTEncoding_Env.bvar_bindings);
                      FStarC_SMTEncoding_Env.fvar_bindings =
                        (env1.FStarC_SMTEncoding_Env.fvar_bindings);
                      FStarC_SMTEncoding_Env.depth =
                        (env1.FStarC_SMTEncoding_Env.depth);
                      FStarC_SMTEncoding_Env.tcenv = env';
                      FStarC_SMTEncoding_Env.warn =
                        (env1.FStarC_SMTEncoding_Env.warn);
                      FStarC_SMTEncoding_Env.nolabels =
                        (env1.FStarC_SMTEncoding_Env.nolabels);
                      FStarC_SMTEncoding_Env.use_zfuel_name =
                        (env1.FStarC_SMTEncoding_Env.use_zfuel_name);
                      FStarC_SMTEncoding_Env.encode_non_total_function_typ =
                        (env1.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
                      FStarC_SMTEncoding_Env.current_module_name =
                        (env1.FStarC_SMTEncoding_Env.current_module_name);
                      FStarC_SMTEncoding_Env.encoding_quantifier =
                        (env1.FStarC_SMTEncoding_Env.encoding_quantifier);
                      FStarC_SMTEncoding_Env.global_cache =
                        (env1.FStarC_SMTEncoding_Env.global_cache)
                    } in
                  let uu___3 =
                    encode_top_level_val false env'1 us
                      (FStar_Pervasives.__proj__Inr__item__v
                         lb.FStarC_Syntax_Syntax.lbname) t quals in
                  (match uu___3 with
                   | (decls', env'2) ->
                       ((FStarC_List.rev_append decls' decls), env'2))))
      ([], env) bindings in
  match uu___ with | (decls, env1) -> ((FStarC_List.rev decls), env1)
exception Let_rec_unencodeable 
let uu___is_Let_rec_unencodeable (projectee : Prims.exn) : Prims.bool=
  match projectee with | Let_rec_unencodeable -> true | uu___ -> false
let copy_env (en : FStarC_SMTEncoding_Env.env_t) :
  FStarC_SMTEncoding_Env.env_t=
  let uu___ = FStarC_SMap.copy en.FStarC_SMTEncoding_Env.global_cache in
  {
    FStarC_SMTEncoding_Env.bvar_bindings =
      (en.FStarC_SMTEncoding_Env.bvar_bindings);
    FStarC_SMTEncoding_Env.fvar_bindings =
      (en.FStarC_SMTEncoding_Env.fvar_bindings);
    FStarC_SMTEncoding_Env.depth = (en.FStarC_SMTEncoding_Env.depth);
    FStarC_SMTEncoding_Env.tcenv = (en.FStarC_SMTEncoding_Env.tcenv);
    FStarC_SMTEncoding_Env.warn = (en.FStarC_SMTEncoding_Env.warn);
    FStarC_SMTEncoding_Env.nolabels = (en.FStarC_SMTEncoding_Env.nolabels);
    FStarC_SMTEncoding_Env.use_zfuel_name =
      (en.FStarC_SMTEncoding_Env.use_zfuel_name);
    FStarC_SMTEncoding_Env.encode_non_total_function_typ =
      (en.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
    FStarC_SMTEncoding_Env.current_module_name =
      (en.FStarC_SMTEncoding_Env.current_module_name);
    FStarC_SMTEncoding_Env.encoding_quantifier =
      (en.FStarC_SMTEncoding_Env.encoding_quantifier);
    FStarC_SMTEncoding_Env.global_cache = uu___
  }
let encode_top_level_let (env : FStarC_SMTEncoding_Env.env_t)
  (uu___ : (Prims.bool * FStarC_Syntax_Syntax.letbinding Prims.list))
  (quals : FStarC_Syntax_Syntax.qualifier Prims.list) :
  (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.env_t)=
  match uu___ with
  | (is_rec, bindings) ->
      let eta_expand binders formals body t =
        let nbinders = FStarC_List.length binders in
        let uu___1 = FStarC_Util.first_N nbinders formals in
        match uu___1 with
        | (formals1, extra_formals) ->
            let subst =
              FStarC_List.map2
                (fun uu___2 uu___3 ->
                   match (uu___2, uu___3) with
                   | ({ FStarC_Syntax_Syntax.binder_bv = formal;
                        FStarC_Syntax_Syntax.binder_qual = uu___4;
                        FStarC_Syntax_Syntax.binder_positivity = uu___5;
                        FStarC_Syntax_Syntax.binder_attrs = uu___6;_},
                      { FStarC_Syntax_Syntax.binder_bv = binder;
                        FStarC_Syntax_Syntax.binder_qual = uu___7;
                        FStarC_Syntax_Syntax.binder_positivity = uu___8;
                        FStarC_Syntax_Syntax.binder_attrs = uu___9;_})
                       ->
                       let uu___10 =
                         let uu___11 = FStarC_Syntax_Syntax.bv_to_name binder in
                         (formal, uu___11) in
                       FStarC_Syntax_Syntax.NT uu___10) formals1 binders in
            let extra_formals1 =
              let uu___2 =
                FStarC_List.map
                  (fun b ->
                     let uu___3 =
                       let uu___4 = b.FStarC_Syntax_Syntax.binder_bv in
                       let uu___5 =
                         FStarC_Syntax_Subst.subst subst
                           (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                       {
                         FStarC_Syntax_Syntax.ppname =
                           (uu___4.FStarC_Syntax_Syntax.ppname);
                         FStarC_Syntax_Syntax.index =
                           (uu___4.FStarC_Syntax_Syntax.index);
                         FStarC_Syntax_Syntax.sort = uu___5
                       } in
                     {
                       FStarC_Syntax_Syntax.binder_bv = uu___3;
                       FStarC_Syntax_Syntax.binder_qual =
                         (b.FStarC_Syntax_Syntax.binder_qual);
                       FStarC_Syntax_Syntax.binder_positivity =
                         (b.FStarC_Syntax_Syntax.binder_positivity);
                       FStarC_Syntax_Syntax.binder_attrs =
                         (b.FStarC_Syntax_Syntax.binder_attrs)
                     }) extra_formals in
              FStarC_Syntax_Util.name_binders uu___2 in
            let body1 =
              let uu___2 = FStarC_Syntax_Subst.compress body in
              let uu___3 =
                let uu___4 =
                  FStarC_Syntax_Util.args_of_binders extra_formals1 in
                FStar_Pervasives_Native.snd uu___4 in
              FStarC_Syntax_Syntax.extend_app_n uu___2 uu___3
                body.FStarC_Syntax_Syntax.pos in
            ((FStarC_List.op_At binders extra_formals1), body1) in
      let destruct_bound_function t e =
        let tcenv =
          let uu___1 = env.FStarC_SMTEncoding_Env.tcenv in
          {
            FStarC_TypeChecker_Env.solver =
              (uu___1.FStarC_TypeChecker_Env.solver);
            FStarC_TypeChecker_Env.range =
              (uu___1.FStarC_TypeChecker_Env.range);
            FStarC_TypeChecker_Env.curmodule =
              (uu___1.FStarC_TypeChecker_Env.curmodule);
            FStarC_TypeChecker_Env.gamma =
              (uu___1.FStarC_TypeChecker_Env.gamma);
            FStarC_TypeChecker_Env.gamma_sig =
              (uu___1.FStarC_TypeChecker_Env.gamma_sig);
            FStarC_TypeChecker_Env.gamma_cache =
              (uu___1.FStarC_TypeChecker_Env.gamma_cache);
            FStarC_TypeChecker_Env.modules =
              (uu___1.FStarC_TypeChecker_Env.modules);
            FStarC_TypeChecker_Env.expected_typ =
              (uu___1.FStarC_TypeChecker_Env.expected_typ);
            FStarC_TypeChecker_Env.sigtab =
              (uu___1.FStarC_TypeChecker_Env.sigtab);
            FStarC_TypeChecker_Env.attrtab =
              (uu___1.FStarC_TypeChecker_Env.attrtab);
            FStarC_TypeChecker_Env.instantiate_imp =
              (uu___1.FStarC_TypeChecker_Env.instantiate_imp);
            FStarC_TypeChecker_Env.effects =
              (uu___1.FStarC_TypeChecker_Env.effects);
            FStarC_TypeChecker_Env.generalize =
              (uu___1.FStarC_TypeChecker_Env.generalize);
            FStarC_TypeChecker_Env.letrecs =
              (uu___1.FStarC_TypeChecker_Env.letrecs);
            FStarC_TypeChecker_Env.top_level =
              (uu___1.FStarC_TypeChecker_Env.top_level);
            FStarC_TypeChecker_Env.check_uvars =
              (uu___1.FStarC_TypeChecker_Env.check_uvars);
            FStarC_TypeChecker_Env.use_eq_strict =
              (uu___1.FStarC_TypeChecker_Env.use_eq_strict);
            FStarC_TypeChecker_Env.is_iface =
              (uu___1.FStarC_TypeChecker_Env.is_iface);
            FStarC_TypeChecker_Env.admit = true;
            FStarC_TypeChecker_Env.phase1 =
              (uu___1.FStarC_TypeChecker_Env.phase1);
            FStarC_TypeChecker_Env.failhard =
              (uu___1.FStarC_TypeChecker_Env.failhard);
            FStarC_TypeChecker_Env.flychecking =
              (uu___1.FStarC_TypeChecker_Env.flychecking);
            FStarC_TypeChecker_Env.uvar_subtyping =
              (uu___1.FStarC_TypeChecker_Env.uvar_subtyping);
            FStarC_TypeChecker_Env.intactics =
              (uu___1.FStarC_TypeChecker_Env.intactics);
            FStarC_TypeChecker_Env.nocoerce =
              (uu___1.FStarC_TypeChecker_Env.nocoerce);
            FStarC_TypeChecker_Env.tc_term =
              (uu___1.FStarC_TypeChecker_Env.tc_term);
            FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
              (uu___1.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStarC_TypeChecker_Env.universe_of =
              (uu___1.FStarC_TypeChecker_Env.universe_of);
            FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (uu___1.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStarC_TypeChecker_Env.teq_nosmt_force =
              (uu___1.FStarC_TypeChecker_Env.teq_nosmt_force);
            FStarC_TypeChecker_Env.subtype_nosmt_force =
              (uu___1.FStarC_TypeChecker_Env.subtype_nosmt_force);
            FStarC_TypeChecker_Env.qtbl_name_and_index =
              (uu___1.FStarC_TypeChecker_Env.qtbl_name_and_index);
            FStarC_TypeChecker_Env.normalized_eff_names =
              (uu___1.FStarC_TypeChecker_Env.normalized_eff_names);
            FStarC_TypeChecker_Env.fv_delta_depths =
              (uu___1.FStarC_TypeChecker_Env.fv_delta_depths);
            FStarC_TypeChecker_Env.proof_ns =
              (uu___1.FStarC_TypeChecker_Env.proof_ns);
            FStarC_TypeChecker_Env.synth_hook =
              (uu___1.FStarC_TypeChecker_Env.synth_hook);
            FStarC_TypeChecker_Env.try_solve_implicits_hook =
              (uu___1.FStarC_TypeChecker_Env.try_solve_implicits_hook);
            FStarC_TypeChecker_Env.splice =
              (uu___1.FStarC_TypeChecker_Env.splice);
            FStarC_TypeChecker_Env.mpreprocess =
              (uu___1.FStarC_TypeChecker_Env.mpreprocess);
            FStarC_TypeChecker_Env.postprocess =
              (uu___1.FStarC_TypeChecker_Env.postprocess);
            FStarC_TypeChecker_Env.identifier_info =
              (uu___1.FStarC_TypeChecker_Env.identifier_info);
            FStarC_TypeChecker_Env.tc_hooks =
              (uu___1.FStarC_TypeChecker_Env.tc_hooks);
            FStarC_TypeChecker_Env.dsenv =
              (uu___1.FStarC_TypeChecker_Env.dsenv);
            FStarC_TypeChecker_Env.nbe = (uu___1.FStarC_TypeChecker_Env.nbe);
            FStarC_TypeChecker_Env.strict_args_tab =
              (uu___1.FStarC_TypeChecker_Env.strict_args_tab);
            FStarC_TypeChecker_Env.erasable_types_tab =
              (uu___1.FStarC_TypeChecker_Env.erasable_types_tab);
            FStarC_TypeChecker_Env.enable_defer_to_tac =
              (uu___1.FStarC_TypeChecker_Env.enable_defer_to_tac);
            FStarC_TypeChecker_Env.unif_allow_ref_guards =
              (uu___1.FStarC_TypeChecker_Env.unif_allow_ref_guards);
            FStarC_TypeChecker_Env.erase_erasable_args =
              (uu___1.FStarC_TypeChecker_Env.erase_erasable_args);
            FStarC_TypeChecker_Env.core_check =
              (uu___1.FStarC_TypeChecker_Env.core_check);
            FStarC_TypeChecker_Env.missing_decl =
              (uu___1.FStarC_TypeChecker_Env.missing_decl)
          } in
        let subst_comp formals actuals comp =
          let subst =
            FStarC_List.map2
              (fun uu___1 uu___2 ->
                 match (uu___1, uu___2) with
                 | ({ FStarC_Syntax_Syntax.binder_bv = x;
                      FStarC_Syntax_Syntax.binder_qual = uu___3;
                      FStarC_Syntax_Syntax.binder_positivity = uu___4;
                      FStarC_Syntax_Syntax.binder_attrs = uu___5;_},
                    { FStarC_Syntax_Syntax.binder_bv = b;
                      FStarC_Syntax_Syntax.binder_qual = uu___6;
                      FStarC_Syntax_Syntax.binder_positivity = uu___7;
                      FStarC_Syntax_Syntax.binder_attrs = uu___8;_})
                     ->
                     let uu___9 =
                       let uu___10 = FStarC_Syntax_Syntax.bv_to_name b in
                       (x, uu___10) in
                     FStarC_Syntax_Syntax.NT uu___9) formals actuals in
          FStarC_Syntax_Subst.subst_comp subst comp in
        let rec arrow_formals_comp_norm norm t1 =
          let t2 =
            let uu___1 = FStarC_Syntax_Subst.compress t1 in
            FStarC_Syntax_Util.unascribe uu___1 in
          match t2.FStarC_Syntax_Syntax.n with
          | FStarC_Syntax_Syntax.Tm_arrow
              { FStarC_Syntax_Syntax.bs1 = formals;
                FStarC_Syntax_Syntax.comp = comp;_}
              -> FStarC_Syntax_Subst.open_comp formals comp
          | FStarC_Syntax_Syntax.Tm_refine uu___1 ->
              let uu___2 = FStarC_Syntax_Util.unrefine t2 in
              arrow_formals_comp_norm norm uu___2
          | uu___1 when Prims.op_Negation norm ->
              let t_norm =
                norm_with_steps
                  [FStarC_TypeChecker_Env.Beta;
                  FStarC_TypeChecker_Env.Weak;
                  FStarC_TypeChecker_Env.HNF;
                  FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
                  FStarC_TypeChecker_Env.UnfoldUntil
                    FStarC_Syntax_Syntax.delta_constant] tcenv t2 in
              arrow_formals_comp_norm true t_norm
          | uu___1 ->
              let uu___2 = FStarC_Syntax_Syntax.mk_Total t2 in ([], uu___2) in
        let aux t1 e1 =
          let uu___1 = FStarC_Syntax_Util.abs_formals e1 in
          match uu___1 with
          | (binders, body, lopt) ->
              let uu___2 =
                match binders with
                | [] -> arrow_formals_comp_norm true t1
                | uu___3 -> arrow_formals_comp_norm false t1 in
              (match uu___2 with
               | (formals, comp) ->
                   let nformals = FStarC_List.length formals in
                   let nbinders = FStarC_List.length binders in
                   let uu___3 =
                     if nformals < nbinders
                     then
                       let uu___4 = FStarC_Util.first_N nformals binders in
                       match uu___4 with
                       | (bs0, rest) ->
                           let body1 = FStarC_Syntax_Util.abs rest body lopt in
                           let uu___5 = subst_comp formals bs0 comp in
                           (bs0, body1, uu___5)
                     else
                       if nformals > nbinders
                       then
                         (let uu___5 =
                            let uu___6 = FStarC_Syntax_Util.comp_result comp in
                            eta_expand binders formals body uu___6 in
                          match uu___5 with
                          | (binders1, body1) ->
                              let uu___6 = subst_comp formals binders1 comp in
                              (binders1, body1, uu___6))
                       else
                         (let uu___6 = subst_comp formals binders comp in
                          (binders, body, uu___6)) in
                   (match uu___3 with
                    | (binders1, body1, comp1) -> (binders1, body1, comp1))) in
        let uu___1 = aux t e in
        match uu___1 with
        | (binders, body, comp) ->
            let uu___2 =
              let tcenv1 = FStarC_TypeChecker_Env.push_binders tcenv binders in
              let uu___3 =
                FStarC_SMTEncoding_Util.is_smt_reifiable_comp tcenv1 comp in
              if uu___3
              then
                let eff_name = FStarC_Syntax_Util.comp_effect_name comp in
                let comp1 =
                  FStarC_TypeChecker_Env.reify_comp tcenv1 comp
                    FStarC_Syntax_Syntax.U_unknown in
                let body1 =
                  let uu___4 =
                    FStarC_Syntax_Util.mk_reify body
                      (FStar_Pervasives_Native.Some eff_name) in
                  FStarC_TypeChecker_Util.norm_reify tcenv1 [] uu___4 in
                let uu___4 = aux comp1 body1 in
                match uu___4 with
                | (more_binders, body2, comp2) ->
                    ((FStarC_List.op_At binders more_binders), body2, comp2)
              else (binders, body, comp) in
            (match uu___2 with
             | (binders1, body1, comp1) ->
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = FStarC_Syntax_Util.comp_result comp1 in
                       FStar_Pervasives.Inl uu___6 in
                     (uu___5, FStar_Pervasives_Native.None, false) in
                   FStarC_Syntax_Util.ascribe body1 uu___4 in
                 (binders1, uu___3, comp1)) in
      (try
         (fun uu___1 ->
            match () with
            | () ->
                let uu___2 =
                  FStarC_Util.for_all
                    (fun lb ->
                       FStarC_Syntax_Util.is_lemma
                         lb.FStarC_Syntax_Syntax.lbtyp) bindings in
                if uu___2
                then encode_top_level_vals env bindings quals
                else
                  (let uu___4 =
                     FStarC_List.fold_left
                       (fun uu___5 lb ->
                          match uu___5 with
                          | (toks, typs, decls, env1) ->
                              ((let uu___7 =
                                  FStarC_Syntax_Util.is_lemma
                                    lb.FStarC_Syntax_Syntax.lbtyp in
                                if uu___7
                                then FStarC_Effect.raise Let_rec_unencodeable
                                else ());
                               (let uu___7 =
                                  FStarC_Syntax_Subst.open_univ_vars
                                    lb.FStarC_Syntax_Syntax.lbunivs
                                    lb.FStarC_Syntax_Syntax.lbtyp in
                                match uu___7 with
                                | (us, t) ->
                                    let env2 =
                                      let uu___8 =
                                        FStarC_TypeChecker_Env.push_univ_vars
                                          env1.FStarC_SMTEncoding_Env.tcenv
                                          us in
                                      {
                                        FStarC_SMTEncoding_Env.bvar_bindings
                                          =
                                          (env1.FStarC_SMTEncoding_Env.bvar_bindings);
                                        FStarC_SMTEncoding_Env.fvar_bindings
                                          =
                                          (env1.FStarC_SMTEncoding_Env.fvar_bindings);
                                        FStarC_SMTEncoding_Env.depth =
                                          (env1.FStarC_SMTEncoding_Env.depth);
                                        FStarC_SMTEncoding_Env.tcenv = uu___8;
                                        FStarC_SMTEncoding_Env.warn =
                                          (env1.FStarC_SMTEncoding_Env.warn);
                                        FStarC_SMTEncoding_Env.nolabels =
                                          (env1.FStarC_SMTEncoding_Env.nolabels);
                                        FStarC_SMTEncoding_Env.use_zfuel_name
                                          =
                                          (env1.FStarC_SMTEncoding_Env.use_zfuel_name);
                                        FStarC_SMTEncoding_Env.encode_non_total_function_typ
                                          =
                                          (env1.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
                                        FStarC_SMTEncoding_Env.current_module_name
                                          =
                                          (env1.FStarC_SMTEncoding_Env.current_module_name);
                                        FStarC_SMTEncoding_Env.encoding_quantifier
                                          =
                                          (env1.FStarC_SMTEncoding_Env.encoding_quantifier);
                                        FStarC_SMTEncoding_Env.global_cache =
                                          (env1.FStarC_SMTEncoding_Env.global_cache)
                                      } in
                                    let t_norm =
                                      if is_rec
                                      then
                                        FStarC_TypeChecker_Normalize.unfold_whnf'
                                          [FStarC_TypeChecker_Env.AllowUnboundUniverses]
                                          env2.FStarC_SMTEncoding_Env.tcenv t
                                      else norm_before_encoding env2 t in
                                    let uu___8 =
                                      declare_top_level_let env2
                                        (FStar_Pervasives.__proj__Inr__item__v
                                           lb.FStarC_Syntax_Syntax.lbname) us
                                        t t_norm in
                                    (match uu___8 with
                                     | (tok, decl, env3) ->
                                         (((tok, us) :: toks), (t_norm ::
                                           typs), (decl :: decls), env3)))))
                       ([], [], [], env) bindings in
                   match uu___4 with
                   | (toks, typs, decls, env1) ->
                       let toks_fvbs = FStarC_List.rev toks in
                       let decls1 =
                         FStarC_List.flatten (FStarC_List.rev decls) in
                       let env_decls = copy_env env1 in
                       let typs1 = FStarC_List.rev typs in
                       let encode_non_rec_lbdef bindings1 typs2 toks1 env2 =
                         match (bindings1, typs2, toks1) with
                         | ({ FStarC_Syntax_Syntax.lbname = lbn;
                              FStarC_Syntax_Syntax.lbunivs = uvs;
                              FStarC_Syntax_Syntax.lbtyp = uu___5;
                              FStarC_Syntax_Syntax.lbeff = uu___6;
                              FStarC_Syntax_Syntax.lbdef = e;
                              FStarC_Syntax_Syntax.lbattrs = uu___7;
                              FStarC_Syntax_Syntax.lbpos = uu___8;_}::[],
                            t_norm::[], (fvb, uu___9)::[]) ->
                             let flid = fvb.FStarC_SMTEncoding_Env.fvar_lid in
                             let uu___10 =
                               FStarC_TypeChecker_Env.open_universes_in
                                 env2.FStarC_SMTEncoding_Env.tcenv uvs
                                 [e; t_norm] in
                             (match uu___10 with
                              | (env', univ_names, e_t) ->
                                  let env'1 =
                                    {
                                      FStarC_SMTEncoding_Env.bvar_bindings =
                                        (env2.FStarC_SMTEncoding_Env.bvar_bindings);
                                      FStarC_SMTEncoding_Env.fvar_bindings =
                                        (env2.FStarC_SMTEncoding_Env.fvar_bindings);
                                      FStarC_SMTEncoding_Env.depth =
                                        (env2.FStarC_SMTEncoding_Env.depth);
                                      FStarC_SMTEncoding_Env.tcenv = env';
                                      FStarC_SMTEncoding_Env.warn =
                                        (env2.FStarC_SMTEncoding_Env.warn);
                                      FStarC_SMTEncoding_Env.nolabels =
                                        (env2.FStarC_SMTEncoding_Env.nolabels);
                                      FStarC_SMTEncoding_Env.use_zfuel_name =
                                        (env2.FStarC_SMTEncoding_Env.use_zfuel_name);
                                      FStarC_SMTEncoding_Env.encode_non_total_function_typ
                                        =
                                        (env2.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
                                      FStarC_SMTEncoding_Env.current_module_name
                                        =
                                        (env2.FStarC_SMTEncoding_Env.current_module_name);
                                      FStarC_SMTEncoding_Env.encoding_quantifier
                                        =
                                        (env2.FStarC_SMTEncoding_Env.encoding_quantifier);
                                      FStarC_SMTEncoding_Env.global_cache =
                                        (env2.FStarC_SMTEncoding_Env.global_cache)
                                    } in
                                  let uu___11 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu___12 -> failwith "Impossible" in
                                  (match uu___11 with
                                   | (e1, t_norm1) ->
                                       let uu___12 =
                                         let uu___13 =
                                           FStarC_List.map
                                             FStarC_SMTEncoding_EncodeTerm.encode_univ_name
                                             univ_names in
                                         FStarC_List.unzip uu___13 in
                                       (match uu___12 with
                                        | (univ_vars, univ_terms) ->
                                            let uu___13 =
                                              destruct_bound_function t_norm1
                                                e1 in
                                            (match uu___13 with
                                             | (binders, body, t_body_comp)
                                                 ->
                                                 let t_body =
                                                   FStarC_Syntax_Util.comp_result
                                                     t_body_comp in
                                                 ((let uu___15 =
                                                     FStarC_Effect.op_Bang
                                                       dbg_SMTEncoding in
                                                   if uu___15
                                                   then
                                                     let uu___16 =
                                                       FStarC_Class_Show.show
                                                         (FStarC_Class_Show.show_list
                                                            FStarC_Syntax_Print.showable_binder)
                                                         binders in
                                                     let uu___17 =
                                                       FStarC_Class_Show.show
                                                         FStarC_Syntax_Print.showable_term
                                                         body in
                                                     FStarC_Format.print2
                                                       "Encoding let : binders=[%s], body=%s\n"
                                                       uu___16 uu___17
                                                   else ());
                                                  (let uu___15 =
                                                     FStarC_SMTEncoding_EncodeTerm.encode_binders
                                                       FStar_Pervasives_Native.None
                                                       binders env'1 in
                                                   match uu___15 with
                                                   | (vars, binder_guards,
                                                      env'2, binder_decls,
                                                      uu___16) ->
                                                       let uu___17 =
                                                         if
                                                           (fvb.FStarC_SMTEncoding_Env.fvb_thunked
                                                              && (vars = []))
                                                             &&
                                                             (univ_vars = [])
                                                         then
                                                           let dummy_var =
                                                             FStarC_SMTEncoding_Term.mk_fv
                                                               ("@dummy",
                                                                 FStarC_SMTEncoding_Term.dummy_sort) in
                                                           let dummy_tm =
                                                             FStarC_SMTEncoding_Term.mkFreeV
                                                               dummy_var
                                                               FStarC_Range_Type.dummyRange in
                                                           let app =
                                                             let uu___18 =
                                                               FStarC_Syntax_Syntax.range_of_lbname
                                                                 lbn in
                                                             FStarC_SMTEncoding_Term.mkApp
                                                               ((fvb.FStarC_SMTEncoding_Env.smt_id),
                                                                 [dummy_tm])
                                                               uu___18 in
                                                           ([dummy_var], app)
                                                         else
                                                           (let uu___19 =
                                                              let uu___20 =
                                                                FStarC_Syntax_Syntax.range_of_lbname
                                                                  lbn in
                                                              let uu___21 =
                                                                let uu___22 =
                                                                  FStarC_List.map
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                FStarC_List.op_At
                                                                  univ_terms
                                                                  uu___22 in
                                                              FStarC_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                uu___20
                                                                {
                                                                  FStarC_SMTEncoding_Env.fvar_lid
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.fvar_lid);
                                                                  FStarC_SMTEncoding_Env.univ_arity
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.univ_arity);
                                                                  FStarC_SMTEncoding_Env.smt_arity
                                                                    =
                                                                    (
                                                                    (FStarC_List.length
                                                                    univ_terms)
                                                                    +
                                                                    fvb.FStarC_SMTEncoding_Env.smt_arity);
                                                                  FStarC_SMTEncoding_Env.smt_id
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.smt_id);
                                                                  FStarC_SMTEncoding_Env.smt_token
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.smt_token);
                                                                  FStarC_SMTEncoding_Env.smt_fuel_partial_app
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.smt_fuel_partial_app);
                                                                  FStarC_SMTEncoding_Env.fvb_thunked
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.fvb_thunked);
                                                                  FStarC_SMTEncoding_Env.needs_fuel_and_universe_instantiations
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.needs_fuel_and_universe_instantiations)
                                                                } uu___21 in
                                                            ((FStarC_List.op_At
                                                                univ_vars
                                                                vars),
                                                              uu___19)) in
                                                       (match uu___17 with
                                                        | (vars1, app) ->
                                                            let is_logical =
                                                              let uu___18 =
                                                                let uu___19 =
                                                                  FStarC_Syntax_Subst.compress
                                                                    t_body in
                                                                uu___19.FStarC_Syntax_Syntax.n in
                                                              match uu___18
                                                              with
                                                              | FStarC_Syntax_Syntax.Tm_fvar
                                                                  fv when
                                                                  FStarC_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    FStarC_Parser_Const.logical_lid
                                                                  -> true
                                                              | uu___19 ->
                                                                  false in
                                                            let is_smt_theory_symbol
                                                              =
                                                              let fv =
                                                                FStar_Pervasives.__proj__Inr__item__v
                                                                  lbn in
                                                              FStarC_TypeChecker_Env.fv_has_attr
                                                                env2.FStarC_SMTEncoding_Env.tcenv
                                                                fv
                                                                FStarC_Parser_Const.smt_theory_symbol_attr_lid in
                                                            let is_sub_singleton
                                                              =
                                                              FStarC_Syntax_Util.is_sub_singleton
                                                                body in
                                                            let should_encode_logical
                                                              =
                                                              (Prims.op_Negation
                                                                 is_smt_theory_symbol)
                                                                &&
                                                                ((FStarC_List.contains
                                                                    FStarC_Syntax_Syntax.Logic
                                                                    quals)
                                                                   ||
                                                                   is_logical) in
                                                            let make_eqn name
                                                              pat app1 body1
                                                              =
                                                              let uu___18 =
                                                                let uu___19 =
                                                                  let uu___20
                                                                    =
                                                                    FStarC_Syntax_Syntax.range_of_lbname
                                                                    lbn in
                                                                  let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    (app1,
                                                                    body1) in
                                                                    ([[pat]],
                                                                    vars1,
                                                                    uu___22) in
                                                                  FStarC_SMTEncoding_Term.mkForall
                                                                    uu___20
                                                                    uu___21 in
                                                                let uu___20 =
                                                                  let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    flid in
                                                                    FStarC_Format.fmt1
                                                                    "Equation for %s"
                                                                    uu___22 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu___21 in
                                                                (uu___19,
                                                                  uu___20,
                                                                  (Prims.strcat
                                                                    name
                                                                    (Prims.strcat
                                                                    "_"
                                                                    fvb.FStarC_SMTEncoding_Env.smt_id))) in
                                                              FStarC_SMTEncoding_Util.mkAssume
                                                                uu___18 in
                                                            let uu___18 =
                                                              let basic_eqn_name
                                                                =
                                                                if
                                                                  should_encode_logical
                                                                then
                                                                  "defn_equation"
                                                                else
                                                                  "equation" in
                                                              let uu___19 =
                                                                let app_is_prop
                                                                  =
                                                                  FStarC_SMTEncoding_Term.mk_subtype_of_unit
                                                                    app in
                                                                if
                                                                  should_encode_logical
                                                                then
                                                                  let uu___20
                                                                    =
                                                                    is_sub_singleton
                                                                    &&
                                                                    (let uu___21
                                                                    =
                                                                    FStarC_Options_Ext.enabled
                                                                    "retain_old_prop_typing" in
                                                                    Prims.op_Negation
                                                                    uu___21) in
                                                                  (if uu___20
                                                                   then
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Syntax_Syntax.range_of_lbname
                                                                    lbn in
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    binder_guards in
                                                                    let uu___29
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_Valid
                                                                    app_is_prop in
                                                                    (uu___28,
                                                                    uu___29) in
                                                                    FStarC_SMTEncoding_Util.mkImp
                                                                    uu___27 in
                                                                    ([
                                                                    [app_is_prop]],
                                                                    vars1,
                                                                    uu___26) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___24
                                                                    uu___25 in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    flid in
                                                                    FStarC_Format.fmt1
                                                                    "Prop-typing for %s"
                                                                    uu___26 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___25 in
                                                                    (uu___23,
                                                                    uu___24,
                                                                    (Prims.strcat
                                                                    basic_eqn_name
                                                                    (Prims.strcat
                                                                    "_"
                                                                    fvb.FStarC_SMTEncoding_Env.smt_id))) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___22 in
                                                                    (uu___21,
                                                                    [])
                                                                   else
                                                                    (let uu___22
                                                                    =
                                                                    FStarC_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'2 in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (body1,
                                                                    decls2)
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    make_eqn
                                                                    basic_eqn_name
                                                                    app_is_prop
                                                                    app body1 in
                                                                    (uu___23,
                                                                    decls2)))
                                                                else
                                                                  (let uu___21
                                                                    =
                                                                    FStarC_SMTEncoding_EncodeTerm.encode_term
                                                                    body
                                                                    env'2 in
                                                                   match uu___21
                                                                   with
                                                                   | 
                                                                   (body1,
                                                                    decls2)
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    make_eqn
                                                                    basic_eqn_name
                                                                    app app
                                                                    body1 in
                                                                    (uu___22,
                                                                    decls2)) in
                                                              match uu___19
                                                              with
                                                              | (basic_eqn,
                                                                 decls2) ->
                                                                  if
                                                                    should_encode_logical
                                                                  then
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_Valid
                                                                    app in
                                                                    let uu___22
                                                                    =
                                                                    FStarC_SMTEncoding_EncodeTerm.encode_formula
                                                                    body
                                                                    env'2 in
                                                                    (app,
                                                                    uu___21,
                                                                    uu___22) in
                                                                    (match uu___20
                                                                    with
                                                                    | 
                                                                    (pat,
                                                                    app1,
                                                                    (body1,
                                                                    decls21))
                                                                    ->
                                                                    let logical_eqn
                                                                    =
                                                                    make_eqn
                                                                    "equation"
                                                                    pat app1
                                                                    body1 in
                                                                    ([logical_eqn;
                                                                    basic_eqn],
                                                                    (FStarC_List.op_At
                                                                    decls2
                                                                    decls21)))
                                                                  else
                                                                    ([basic_eqn],
                                                                    decls2) in
                                                            (match uu___18
                                                             with
                                                             | (eqns, decls2)
                                                                 ->
                                                                 let uu___19
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
                                                                    primitive_type_axioms
                                                                    env2.FStarC_SMTEncoding_Env.tcenv
                                                                    flid
                                                                    fvb.FStarC_SMTEncoding_Env.smt_id
                                                                    app in
                                                                    FStarC_List.op_At
                                                                    eqns
                                                                    uu___24 in
                                                                    FStarC_SMTEncoding_Term.mk_decls_trivial
                                                                    uu___23 in
                                                                    FStarC_List.op_At
                                                                    decls2
                                                                    uu___22 in
                                                                    FStarC_List.op_At
                                                                    binder_decls
                                                                    uu___21 in
                                                                   FStarC_List.op_At
                                                                    decls1
                                                                    uu___20 in
                                                                 (uu___19,
                                                                   env2)))))))))
                         | uu___5 -> failwith "Impossible" in
                       let encode_rec_lbdefs bindings1 typs2 toks1 env2 =
                         let fuel =
                           let uu___5 =
                             let uu___6 =
                               FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.fresh
                                 env2.FStarC_SMTEncoding_Env.current_module_name
                                 "fuel" in
                             (uu___6, FStarC_SMTEncoding_Term.Fuel_sort) in
                           FStarC_SMTEncoding_Term.mk_fv uu___5 in
                         let fuel_tm = FStarC_SMTEncoding_Util.mkFreeV fuel in
                         let env0 = env2 in
                         let uu___5 =
                           FStarC_List.fold_left
                             (fun uu___6 uu___7 ->
                                match (uu___6, uu___7) with
                                | ((gtoks, env3), (fvb, univ_names)) ->
                                    let flid =
                                      fvb.FStarC_SMTEncoding_Env.fvar_lid in
                                    let g =
                                      let uu___8 =
                                        FStarC_Ident.lid_add_suffix flid
                                          "fuel_instrumented" in
                                      FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.new_fvar
                                        uu___8 in
                                    let gtok =
                                      let uu___8 =
                                        FStarC_Ident.lid_add_suffix flid
                                          "fuel_instrumented_token" in
                                      FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.new_fvar
                                        uu___8 in
                                    let env4 =
                                      let uu___8 =
                                        let uu___9 =
                                          FStarC_SMTEncoding_Util.mkApp
                                            (g, [fuel_tm]) in
                                        FStar_Pervasives_Native.Some uu___9 in
                                      FStarC_SMTEncoding_Env.push_free_var_tok_with_fuel_and_univs
                                        env3 flid
                                        fvb.FStarC_SMTEncoding_Env.smt_arity
                                        fvb.FStarC_SMTEncoding_Env.univ_arity
                                        gtok uu___8 univ_names in
                                    (((fvb, g, gtok) :: gtoks), env4))
                             ([], env2) toks1 in
                         match uu___5 with
                         | (gtoks, env3) ->
                             let gtoks1 = FStarC_List.rev gtoks in
                             let encode_one_binding env01 uu___6 t_norm
                               uu___7 =
                               match (uu___6, uu___7) with
                               | ((fvb, g, gtok),
                                  { FStarC_Syntax_Syntax.lbname = lbn;
                                    FStarC_Syntax_Syntax.lbunivs = uvs;
                                    FStarC_Syntax_Syntax.lbtyp = uu___8;
                                    FStarC_Syntax_Syntax.lbeff = uu___9;
                                    FStarC_Syntax_Syntax.lbdef = e;
                                    FStarC_Syntax_Syntax.lbattrs = uu___10;
                                    FStarC_Syntax_Syntax.lbpos = uu___11;_})
                                   ->
                                   let uu___12 =
                                     let uu___13 =
                                       FStarC_TypeChecker_Env.open_universes_in
                                         env3.FStarC_SMTEncoding_Env.tcenv
                                         uvs [e; t_norm] in
                                     match uu___13 with
                                     | (env', univ_names, e1::t_norm1::[]) ->
                                         let uu___14 =
                                           let uu___15 =
                                             FStarC_List.map
                                               FStarC_SMTEncoding_EncodeTerm.encode_univ_name
                                               univ_names in
                                           FStarC_List.unzip uu___15 in
                                         (match uu___14 with
                                          | (univ_vars, uu___15) ->
                                              ({
                                                 FStarC_SMTEncoding_Env.bvar_bindings
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.bvar_bindings);
                                                 FStarC_SMTEncoding_Env.fvar_bindings
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.fvar_bindings);
                                                 FStarC_SMTEncoding_Env.depth
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.depth);
                                                 FStarC_SMTEncoding_Env.tcenv
                                                   = env';
                                                 FStarC_SMTEncoding_Env.warn
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.warn);
                                                 FStarC_SMTEncoding_Env.nolabels
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.nolabels);
                                                 FStarC_SMTEncoding_Env.use_zfuel_name
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.use_zfuel_name);
                                                 FStarC_SMTEncoding_Env.encode_non_total_function_typ
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
                                                 FStarC_SMTEncoding_Env.current_module_name
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.current_module_name);
                                                 FStarC_SMTEncoding_Env.encoding_quantifier
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.encoding_quantifier);
                                                 FStarC_SMTEncoding_Env.global_cache
                                                   =
                                                   (env3.FStarC_SMTEncoding_Env.global_cache)
                                               }, e1, univ_vars, t_norm1)) in
                                   (match uu___12 with
                                    | (env', e1, univ_vars, t_norm1) ->
                                        ((let uu___14 =
                                            FStarC_Effect.op_Bang
                                              dbg_SMTEncoding in
                                          if uu___14
                                          then
                                            let uu___15 =
                                              FStarC_Class_Show.show
                                                (FStarC_Class_Show.show_either
                                                   FStarC_Syntax_Print.showable_bv
                                                   FStarC_Syntax_Syntax.showable_fv)
                                                lbn in
                                            let uu___16 =
                                              FStarC_Class_Show.show
                                                FStarC_Syntax_Print.showable_term
                                                t_norm1 in
                                            let uu___17 =
                                              FStarC_Class_Show.show
                                                FStarC_Syntax_Print.showable_term
                                                e1 in
                                            FStarC_Format.print3
                                              "Encoding let rec %s : %s = %s\n"
                                              uu___15 uu___16 uu___17
                                          else ());
                                         (let uu___14 =
                                            destruct_bound_function t_norm1
                                              e1 in
                                          match uu___14 with
                                          | (binders, body, tres_comp) ->
                                              let curry =
                                                fvb.FStarC_SMTEncoding_Env.smt_arity
                                                  <>
                                                  (FStarC_List.length binders) in
                                              let uu___15 =
                                                FStarC_TypeChecker_Util.pure_or_ghost_pre_and_post
                                                  env3.FStarC_SMTEncoding_Env.tcenv
                                                  tres_comp in
                                              (match uu___15 with
                                               | (pre_opt, tres) ->
                                                   ((let uu___17 =
                                                       FStarC_Effect.op_Bang
                                                         dbg_SMTEncoding in
                                                     if uu___17
                                                     then
                                                       let uu___18 =
                                                         FStarC_Class_Show.show
                                                           (FStarC_Class_Show.show_either
                                                              FStarC_Syntax_Print.showable_bv
                                                              FStarC_Syntax_Syntax.showable_fv)
                                                           lbn in
                                                       let uu___19 =
                                                         FStarC_Class_Show.show
                                                           (FStarC_Class_Show.show_list
                                                              FStarC_Syntax_Print.showable_binder)
                                                           binders in
                                                       let uu___20 =
                                                         FStarC_Class_Show.show
                                                           FStarC_Syntax_Print.showable_term
                                                           body in
                                                       let uu___21 =
                                                         FStarC_Class_Show.show
                                                           FStarC_Syntax_Print.showable_comp
                                                           tres_comp in
                                                       FStarC_Format.print4
                                                         "Encoding let rec %s: \n\tbinders=[%s], \n\tbody=%s, \n\ttres=%s\n"
                                                         uu___18 uu___19
                                                         uu___20 uu___21
                                                     else ());
                                                    (let uu___17 =
                                                       FStarC_SMTEncoding_EncodeTerm.encode_binders
                                                         FStar_Pervasives_Native.None
                                                         binders env' in
                                                     match uu___17 with
                                                     | (vars, guards, env'1,
                                                        binder_decls,
                                                        uu___18) ->
                                                         let uu___19 =
                                                           match pre_opt with
                                                           | FStar_Pervasives_Native.None
                                                               ->
                                                               let uu___20 =
                                                                 FStarC_SMTEncoding_Util.mk_and_l
                                                                   guards in
                                                               (uu___20, [])
                                                           | FStar_Pervasives_Native.Some
                                                               pre ->
                                                               let uu___20 =
                                                                 FStarC_SMTEncoding_EncodeTerm.encode_formula
                                                                   pre env'1 in
                                                               (match uu___20
                                                                with
                                                                | (guard,
                                                                   decls0) ->
                                                                    let uu___21
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    (FStarC_List.op_At
                                                                    guards
                                                                    [guard]) in
                                                                    (uu___21,
                                                                    decls0)) in
                                                         (match uu___19 with
                                                          | (guard,
                                                             guard_decls) ->
                                                              let binder_decls1
                                                                =
                                                                FStarC_List.op_At
                                                                  binder_decls
                                                                  guard_decls in
                                                              let univ_sorts
                                                                =
                                                                FStarC_List.map
                                                                  FStarC_SMTEncoding_Term.fv_sort
                                                                  univ_vars in
                                                              let decl_g =
                                                                let uu___20 =
                                                                  let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Util.first_N
                                                                    fvb.FStarC_SMTEncoding_Env.smt_arity
                                                                    vars in
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___24 in
                                                                    FStarC_List.map
                                                                    FStarC_SMTEncoding_Term.fv_sort
                                                                    uu___23 in
                                                                    FStarC_List.op_At
                                                                    (FStarC_SMTEncoding_Term.Fuel_sort
                                                                    ::
                                                                    univ_sorts)
                                                                    uu___22 in
                                                                  (g,
                                                                    uu___21,
                                                                    FStarC_SMTEncoding_Term.Term_sort,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel-instrumented function name")) in
                                                                FStarC_SMTEncoding_Term.DeclFun
                                                                  uu___20 in
                                                              let env02 =
                                                                FStarC_SMTEncoding_Env.push_zfuel_name
                                                                  env01
                                                                  fvb.FStarC_SMTEncoding_Env.fvar_lid
                                                                  g gtok in
                                                              let decl_g_tok
                                                                =
                                                                FStarC_SMTEncoding_Term.DeclFun
                                                                  (gtok,
                                                                    univ_sorts,
                                                                    FStarC_SMTEncoding_Term.Term_sort,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Token for fuel-instrumented partial applications")) in
                                                              let univ_vars_tm
                                                                =
                                                                FStarC_List.map
                                                                  FStarC_SMTEncoding_Util.mkFreeV
                                                                  univ_vars in
                                                              let vars_tm =
                                                                FStarC_List.map
                                                                  FStarC_SMTEncoding_Util.mkFreeV
                                                                  vars in
                                                              let rng =
                                                                FStarC_Syntax_Syntax.range_of_lbname
                                                                  lbn in
                                                              let fvb_with_univs_arity
                                                                =
                                                                {
                                                                  FStarC_SMTEncoding_Env.fvar_lid
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.fvar_lid);
                                                                  FStarC_SMTEncoding_Env.univ_arity
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.univ_arity);
                                                                  FStarC_SMTEncoding_Env.smt_arity
                                                                    =
                                                                    (
                                                                    (FStarC_List.length
                                                                    univ_vars)
                                                                    +
                                                                    fvb.FStarC_SMTEncoding_Env.smt_arity);
                                                                  FStarC_SMTEncoding_Env.smt_id
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.smt_id);
                                                                  FStarC_SMTEncoding_Env.smt_token
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.smt_token);
                                                                  FStarC_SMTEncoding_Env.smt_fuel_partial_app
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.smt_fuel_partial_app);
                                                                  FStarC_SMTEncoding_Env.fvb_thunked
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.fvb_thunked);
                                                                  FStarC_SMTEncoding_Env.needs_fuel_and_universe_instantiations
                                                                    =
                                                                    (
                                                                    fvb.FStarC_SMTEncoding_Env.needs_fuel_and_universe_instantiations)
                                                                } in
                                                              let app =
                                                                let uu___20 =
                                                                  FStarC_List.map
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    (
                                                                    FStarC_List.op_At
                                                                    univ_vars
                                                                    vars) in
                                                                FStarC_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                  rng
                                                                  fvb_with_univs_arity
                                                                  uu___20 in
                                                              let mk_g_app
                                                                args =
                                                                FStarC_SMTEncoding_EncodeTerm.maybe_curry_app
                                                                  rng
                                                                  (FStar_Pervasives.Inl
                                                                    (FStarC_SMTEncoding_Term.Var
                                                                    g))
                                                                  (fvb_with_univs_arity.FStarC_SMTEncoding_Env.smt_arity
                                                                    +
                                                                    Prims.int_one)
                                                                  args in
                                                              let gsapp =
                                                                let uu___20 =
                                                                  let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkApp
                                                                    ("SFuel",
                                                                    [fuel_tm]) in
                                                                    uu___22
                                                                    ::
                                                                    univ_vars_tm in
                                                                  FStarC_List.op_At
                                                                    uu___21
                                                                    vars_tm in
                                                                mk_g_app
                                                                  uu___20 in
                                                              let gmax =
                                                                let uu___20 =
                                                                  let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkApp
                                                                    ("MaxFuel",
                                                                    []) in
                                                                    uu___22
                                                                    ::
                                                                    univ_vars_tm in
                                                                  FStarC_List.op_At
                                                                    uu___21
                                                                    vars_tm in
                                                                mk_g_app
                                                                  uu___20 in
                                                              let uu___20 =
                                                                FStarC_SMTEncoding_EncodeTerm.encode_term
                                                                  body env'1 in
                                                              (match uu___20
                                                               with
                                                               | (body_tm,
                                                                  decls2) ->
                                                                   let eqn_g
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Syntax.range_of_lbname
                                                                    lbn in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                    (guard,
                                                                    uu___27) in
                                                                    FStarC_SMTEncoding_Util.mkImp
                                                                    uu___26 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    Prims.int_zero),
                                                                    (fuel ::
                                                                    (FStarC_List.op_At
                                                                    univ_vars
                                                                    vars)),
                                                                    uu___25) in
                                                                    FStarC_SMTEncoding_Term.mkForall'
                                                                    uu___23
                                                                    uu___24 in
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    fvb.FStarC_SMTEncoding_Env.fvar_lid in
                                                                    FStarC_Format.fmt1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    uu___25 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___24 in
                                                                    (uu___22,
                                                                    uu___23,
                                                                    (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___21 in
                                                                   let eqn_f
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Syntax.range_of_lbname
                                                                    lbn in
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                    ([[app]],
                                                                    (FStarC_List.op_At
                                                                    univ_vars
                                                                    vars),
                                                                    uu___25) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___23
                                                                    uu___24 in
                                                                    (uu___22,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                    (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___21 in
                                                                   let eqn_g'
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Syntax.range_of_lbname
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
                                                                    FStarC_SMTEncoding_Term.n_fuel
                                                                    Prims.int_zero in
                                                                    uu___29
                                                                    ::
                                                                    (FStarC_List.op_At
                                                                    univ_vars_tm
                                                                    vars_tm) in
                                                                    mk_g_app
                                                                    uu___28 in
                                                                    (gsapp,
                                                                    uu___27) in
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    uu___26 in
                                                                    ([
                                                                    [gsapp]],
                                                                    (fuel ::
                                                                    (FStarC_List.op_At
                                                                    univ_vars
                                                                    vars)),
                                                                    uu___25) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___23
                                                                    uu___24 in
                                                                    (uu___22,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                    (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___21 in
                                                                   let uu___21
                                                                    =
                                                                    let gapp
                                                                    =
                                                                    mk_g_app
                                                                    (fuel_tm
                                                                    ::
                                                                    (FStarC_List.op_At
                                                                    univ_vars_tm
                                                                    vars_tm)) in
                                                                    let tok_corr
                                                                    =
                                                                    let gtok_univs_app
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkApp'
                                                                    ((FStarC_SMTEncoding_Term.Var
                                                                    gtok),
                                                                    univ_vars_tm) in
                                                                    let tok_app
                                                                    =
                                                                    FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                                                    gtok_univs_app
                                                                    (fuel ::
                                                                    vars) in
                                                                    let tot_fun_axioms
                                                                    =
                                                                    let head
                                                                    =
                                                                    gtok_univs_app in
                                                                    let vars1
                                                                    = fuel ::
                                                                    vars in
                                                                    let guards1
                                                                    =
                                                                    FStarC_List.map
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStarC_SMTEncoding_Util.mkTrue)
                                                                    vars1 in
                                                                    let tot_fun_axioms1
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Syntax_Util.is_pure_comp
                                                                    tres_comp in
                                                                    FStarC_SMTEncoding_EncodeTerm.isTotFun_axioms
                                                                    rng head
                                                                    [] vars1
                                                                    guards1
                                                                    uu___22 in
                                                                    match univ_vars
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    tot_fun_axioms1
                                                                    | 
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Syntax_Syntax.range_of_lbname
                                                                    lbn in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___23
                                                                    ([],
                                                                    univ_vars,
                                                                    tot_fun_axioms1) in
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
                                                                    FStarC_Syntax_Syntax.range_of_lbname
                                                                    lbn in
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    (FStarC_List.op_At
                                                                    univ_vars
                                                                    vars)),
                                                                    uu___28) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___26
                                                                    uu___27 in
                                                                    (uu___25,
                                                                    tot_fun_axioms) in
                                                                    FStarC_SMTEncoding_Util.mkAnd
                                                                    uu___24 in
                                                                    (uu___23,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___22 in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_SMTEncoding_EncodeTerm.encode_term_pred
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
                                                                    FStarC_Syntax_Syntax.range_of_lbname
                                                                    lbn in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkImp
                                                                    (guard,
                                                                    g_typing) in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    (FStarC_List.op_At
                                                                    univ_vars
                                                                    vars)),
                                                                    uu___30) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___28
                                                                    uu___29 in
                                                                    (uu___27,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
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
                                                                    (FStarC_List.op_At
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
                                                                    FStarC_SMTEncoding_Term.mk_decls_trivial
                                                                    [decl_g;
                                                                    decl_g_tok] in
                                                                    FStarC_List.op_At
                                                                    aux_decls
                                                                    uu___25 in
                                                                    FStarC_List.op_At
                                                                    decls2
                                                                    uu___24 in
                                                                    FStarC_List.op_At
                                                                    binder_decls1
                                                                    uu___23 in
                                                                    let uu___23
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_decls_trivial
                                                                    (FStarC_List.op_At
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing) in
                                                                    (uu___22,
                                                                    uu___23,
                                                                    env02)))))))))) in
                             let uu___6 =
                               let uu___7 =
                                 FStarC_List.zip3 gtoks1 typs2 bindings1 in
                               FStarC_List.fold_left
                                 (fun uu___8 uu___9 ->
                                    match (uu___8, uu___9) with
                                    | ((decls2, eqns, env01), (gtok, ty, lb))
                                        ->
                                        let uu___10 =
                                          encode_one_binding env01 gtok ty lb in
                                        (match uu___10 with
                                         | (decls', eqns', env02) ->
                                             ((decls' :: decls2),
                                               (FStarC_List.op_At eqns' eqns),
                                               env02))) ([decls1], [], env0)
                                 uu___7 in
                             (match uu___6 with
                              | (decls2, eqns, env01) ->
                                  let uu___7 =
                                    let isDeclFun uu___8 =
                                      match uu___8 with
                                      | FStarC_SMTEncoding_Term.DeclFun
                                          uu___9 -> true
                                      | uu___9 -> false in
                                    let uu___8 =
                                      FStarC_List.fold_left
                                        (fun uu___9 elt ->
                                           match uu___9 with
                                           | (prefix_decls, elts, rest) ->
                                               let uu___10 =
                                                 (FStar_Pervasives_Native.uu___is_Some
                                                    elt.FStarC_SMTEncoding_Term.key)
                                                   &&
                                                   (FStarC_List.existsb
                                                      isDeclFun
                                                      elt.FStarC_SMTEncoding_Term.decls) in
                                               if uu___10
                                               then
                                                 (prefix_decls,
                                                   (FStarC_List.op_At elts
                                                      [elt]), rest)
                                               else
                                                 (let uu___12 =
                                                    FStarC_List.partition
                                                      isDeclFun
                                                      elt.FStarC_SMTEncoding_Term.decls in
                                                  match uu___12 with
                                                  | (elt_decl_funs, elt_rest)
                                                      ->
                                                      ((FStarC_List.op_At
                                                          prefix_decls
                                                          elt_decl_funs),
                                                        elts,
                                                        (FStarC_List.op_At
                                                           rest
                                                           [{
                                                              FStarC_SMTEncoding_Term.sym_name
                                                                =
                                                                (elt.FStarC_SMTEncoding_Term.sym_name);
                                                              FStarC_SMTEncoding_Term.key
                                                                =
                                                                (elt.FStarC_SMTEncoding_Term.key);
                                                              FStarC_SMTEncoding_Term.decls
                                                                = elt_rest;
                                                              FStarC_SMTEncoding_Term.a_names
                                                                =
                                                                (elt.FStarC_SMTEncoding_Term.a_names)
                                                            }]))))
                                        ([], [], [])
                                        (FStarC_List.flatten decls2) in
                                    match uu___8 with
                                    | (prefix_decls, elts, rest) ->
                                        let uu___9 =
                                          FStarC_SMTEncoding_Term.mk_decls_trivial
                                            prefix_decls in
                                        (uu___9, elts, rest) in
                                  (match uu___7 with
                                   | (prefix_decls, elts, rest) ->
                                       let eqns1 = FStarC_List.rev eqns in
                                       ((FStarC_List.op_At prefix_decls
                                           (FStarC_List.op_At elts
                                              (FStarC_List.op_At rest eqns1))),
                                         env01))) in
                       let uu___5 =
                         (FStarC_Util.for_some
                            (fun uu___6 ->
                               match uu___6 with
                               | FStarC_Syntax_Syntax.HasMaskedEffect -> true
                               | uu___7 -> false) quals)
                           ||
                           (FStarC_Util.for_some
                              (fun t ->
                                 let uu___6 =
                                   (FStarC_Syntax_Util.is_pure_or_ghost_function
                                      t)
                                     ||
                                     (FStarC_SMTEncoding_Util.is_smt_reifiable_function
                                        env1.FStarC_SMTEncoding_Env.tcenv t) in
                                 Prims.op_Negation uu___6) typs1) in
                       if uu___5
                       then (decls1, env_decls)
                       else
                         if Prims.op_Negation is_rec
                         then
                           encode_non_rec_lbdef bindings typs1 toks_fvbs env1
                         else encode_rec_lbdefs bindings typs1 toks_fvbs env1))
           ()
       with
       | Let_rec_unencodeable ->
           let msg =
             let uu___2 =
               FStarC_List.map
                 (fun lb ->
                    FStarC_Class_Show.show
                      (FStarC_Class_Show.show_either
                         FStarC_Syntax_Print.showable_bv
                         FStarC_Syntax_Syntax.showable_fv)
                      lb.FStarC_Syntax_Syntax.lbname) bindings in
             FStarC_String.concat " and " uu___2 in
           let decl =
             FStarC_SMTEncoding_Term.Caption
               (Prims.strcat "let rec unencodeable: Skipping: " msg) in
           let uu___2 = FStarC_SMTEncoding_Term.mk_decls_trivial [decl] in
           (uu___2, env))
let encode_sig_inductive (env : FStarC_SMTEncoding_Env.env_t)
  (se : FStarC_Syntax_Syntax.sigelt) :
  (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.env_t)=
  let uu___ = se.FStarC_Syntax_Syntax.sigel in
  match uu___ with
  | FStarC_Syntax_Syntax.Sig_inductive_typ
      { FStarC_Syntax_Syntax.lid = t;
        FStarC_Syntax_Syntax.us = universe_names;
        FStarC_Syntax_Syntax.params = tps;
        FStarC_Syntax_Syntax.num_uniform_params = uu___1;
        FStarC_Syntax_Syntax.t = k; FStarC_Syntax_Syntax.mutuals = uu___2;
        FStarC_Syntax_Syntax.ds = datas;
        FStarC_Syntax_Syntax.injective_type_params = injective_type_params;_}
      ->
      let uu___3 = FStarC_Syntax_Subst.univ_var_opening universe_names in
      (match uu___3 with
       | (usubst, uvs) ->
           let env1 =
             let uu___4 =
               FStarC_TypeChecker_Env.push_univ_vars
                 env.FStarC_SMTEncoding_Env.tcenv uvs in
             {
               FStarC_SMTEncoding_Env.bvar_bindings =
                 (env.FStarC_SMTEncoding_Env.bvar_bindings);
               FStarC_SMTEncoding_Env.fvar_bindings =
                 (env.FStarC_SMTEncoding_Env.fvar_bindings);
               FStarC_SMTEncoding_Env.depth =
                 (env.FStarC_SMTEncoding_Env.depth);
               FStarC_SMTEncoding_Env.tcenv = uu___4;
               FStarC_SMTEncoding_Env.warn =
                 (env.FStarC_SMTEncoding_Env.warn);
               FStarC_SMTEncoding_Env.nolabels =
                 (env.FStarC_SMTEncoding_Env.nolabels);
               FStarC_SMTEncoding_Env.use_zfuel_name =
                 (env.FStarC_SMTEncoding_Env.use_zfuel_name);
               FStarC_SMTEncoding_Env.encode_non_total_function_typ =
                 (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
               FStarC_SMTEncoding_Env.current_module_name =
                 (env.FStarC_SMTEncoding_Env.current_module_name);
               FStarC_SMTEncoding_Env.encoding_quantifier =
                 (env.FStarC_SMTEncoding_Env.encoding_quantifier);
               FStarC_SMTEncoding_Env.global_cache =
                 (env.FStarC_SMTEncoding_Env.global_cache)
             } in
           let tps1 = FStarC_Syntax_Subst.subst_binders usubst tps in
           let k1 =
             let uu___4 =
               FStarC_Syntax_Subst.shift_subst (FStarC_List.length tps1)
                 usubst in
             FStarC_Syntax_Subst.subst uu___4 k in
           let uu___4 =
             let uu___5 =
               FStarC_List.map FStarC_SMTEncoding_EncodeTerm.encode_univ_name
                 uvs in
             FStarC_List.unzip uu___5 in
           (match uu___4 with
            | (univ_vars, univ_terms) ->
                let univ_arity =
                  FStarC_List.map
                    (fun uu___5 -> FStarC_SMTEncoding_Term.univ_sort)
                    univ_vars in
                let t_lid = t in
                let tcenv = env1.FStarC_SMTEncoding_Env.tcenv in
                let quals = se.FStarC_Syntax_Syntax.sigquals in
                let is_logical =
                  FStarC_Util.for_some
                    (fun uu___5 ->
                       match uu___5 with
                       | FStarC_Syntax_Syntax.Logic -> true
                       | FStarC_Syntax_Syntax.Assumption -> true
                       | uu___6 -> false) quals in
                let constructor_or_logic_type_decl c =
                  if is_logical
                  then
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStarC_List.map
                            (fun f -> f.FStarC_SMTEncoding_Term.field_sort)
                            c.FStarC_SMTEncoding_Term.constr_fields in
                        ((c.FStarC_SMTEncoding_Term.constr_name), uu___7,
                          FStarC_SMTEncoding_Term.Term_sort,
                          FStar_Pervasives_Native.None) in
                      FStarC_SMTEncoding_Term.DeclFun uu___6 in
                    [uu___5]
                  else
                    (let uu___6 = FStarC_Ident.range_of_lid t in
                     FStarC_SMTEncoding_Term.constructor_to_decl uu___6 c) in
                let inversion_axioms env2 tapp vars =
                  let uu___5 =
                    FStarC_Util.for_some
                      (fun l ->
                         let uu___6 =
                           FStarC_TypeChecker_Env.try_lookup_lid
                             env2.FStarC_SMTEncoding_Env.tcenv l in
                         FStar_Pervasives_Native.uu___is_None uu___6) datas in
                  if uu___5
                  then []
                  else
                    (let uu___7 =
                       FStarC_SMTEncoding_Env.fresh_fvar
                         env2.FStarC_SMTEncoding_Env.current_module_name "x"
                         FStarC_SMTEncoding_Term.Term_sort in
                     match uu___7 with
                     | (xxsym, xx) ->
                         let uu___8 =
                           FStarC_List.fold_left
                             (fun uu___9 l ->
                                match uu___9 with
                                | (out, decls) ->
                                    let is_l =
                                      FStarC_SMTEncoding_Env.mk_data_tester
                                        env2 l xx in
                                    let univ_eqs =
                                      FStarC_List.mapi
                                        (fun i u ->
                                           let uu___10 =
                                             let uu___11 =
                                               FStarC_SMTEncoding_Util.mkFreeV
                                                 u in
                                             let uu___12 =
                                               let uu___13 =
                                                 let uu___14 =
                                                   FStarC_SMTEncoding_Env.mk_univ_projector_name
                                                     l i in
                                                 (uu___14, [xx]) in
                                               FStarC_SMTEncoding_Util.mkApp
                                                 uu___13 in
                                             (uu___11, uu___12) in
                                           FStarC_SMTEncoding_Util.mkEq
                                             uu___10) univ_vars in
                                    let base_eqs = is_l :: univ_eqs in
                                    let uu___10 =
                                      let uu___11 =
                                        injective_type_params ||
                                          (FStarC_Options_Ext.enabled
                                             "compat:injectivity") in
                                      if uu___11
                                      then
                                        let uu___12 =
                                          FStarC_TypeChecker_Env.lookup_datacon
                                            env2.FStarC_SMTEncoding_Env.tcenv
                                            l in
                                        match uu___12 with
                                        | (_univs, data_t) ->
                                            let uu___13 =
                                              FStarC_Syntax_Util.arrow_formals
                                                data_t in
                                            (match uu___13 with
                                             | (args, res) ->
                                                 let params_and_indices =
                                                   let uu___14 =
                                                     FStarC_Syntax_Util.head_and_args_full
                                                       res in
                                                   FStar_Pervasives_Native.snd
                                                     uu___14 in
                                                 let env3 =
                                                   FStarC_List.fold_left
                                                     (fun env4 uu___14 ->
                                                        match uu___14 with
                                                        | {
                                                            FStarC_Syntax_Syntax.binder_bv
                                                              = x;
                                                            FStarC_Syntax_Syntax.binder_qual
                                                              = uu___15;
                                                            FStarC_Syntax_Syntax.binder_positivity
                                                              = uu___16;
                                                            FStarC_Syntax_Syntax.binder_attrs
                                                              = uu___17;_}
                                                            ->
                                                            let uu___18 =
                                                              let uu___19 =
                                                                let uu___20 =
                                                                  FStarC_SMTEncoding_Env.mk_term_projector_name
                                                                    l x in
                                                                (uu___20,
                                                                  [xx]) in
                                                              FStarC_SMTEncoding_Util.mkApp
                                                                uu___19 in
                                                            FStarC_SMTEncoding_Env.push_term_var
                                                              env4 x uu___18)
                                                     env2 args in
                                                 let uu___14 =
                                                   FStarC_SMTEncoding_EncodeTerm.encode_args
                                                     params_and_indices env3 in
                                                 (match uu___14 with
                                                  | (params_and_indices1,
                                                     decls') ->
                                                      (if
                                                         (FStarC_List.length
                                                            params_and_indices1)
                                                           <>
                                                           (FStarC_List.length
                                                              vars)
                                                       then
                                                         failwith
                                                           "Impossible"
                                                       else ();
                                                       (let eqs =
                                                          FStarC_List.map2
                                                            (fun v a ->
                                                               let uu___16 =
                                                                 let uu___17
                                                                   =
                                                                   FStarC_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                 (uu___17, a) in
                                                               FStarC_SMTEncoding_Util.mkEq
                                                                 uu___16)
                                                            vars
                                                            params_and_indices1 in
                                                        let uu___16 =
                                                          FStarC_SMTEncoding_Util.mk_and_l
                                                            (FStarC_List.op_At
                                                               base_eqs eqs) in
                                                        (uu___16, decls')))))
                                      else
                                        (let uu___13 =
                                           FStarC_SMTEncoding_Util.mk_and_l
                                             base_eqs in
                                         (uu___13, [])) in
                                    (match uu___10 with
                                     | (inversion_case, decls') ->
                                         let uu___11 =
                                           FStarC_SMTEncoding_Util.mkOr
                                             (out, inversion_case) in
                                         (uu___11,
                                           (FStarC_List.op_At decls decls'))))
                             (FStarC_SMTEncoding_Util.mkFalse, []) datas in
                         (match uu___8 with
                          | (data_ax, decls) ->
                              let uu___9 =
                                FStarC_SMTEncoding_Env.fresh_fvar
                                  env2.FStarC_SMTEncoding_Env.current_module_name
                                  "f" FStarC_SMTEncoding_Term.Fuel_sort in
                              (match uu___9 with
                               | (ffsym, ff) ->
                                   let fuel_guarded_inversion =
                                     let xx_has_type_sfuel =
                                       if
                                         (FStarC_List.length datas) >
                                           Prims.int_one
                                       then
                                         let uu___10 =
                                           FStarC_SMTEncoding_Util.mkApp
                                             ("SFuel", [ff]) in
                                         FStarC_SMTEncoding_Term.mk_HasTypeFuel
                                           uu___10 xx tapp
                                       else
                                         FStarC_SMTEncoding_Term.mk_HasTypeFuel
                                           ff xx tapp in
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 =
                                           FStarC_Ident.range_of_lid t in
                                         let uu___13 =
                                           let uu___14 =
                                             let uu___15 =
                                               FStarC_SMTEncoding_Term.mk_fv
                                                 (ffsym,
                                                   FStarC_SMTEncoding_Term.Fuel_sort) in
                                             let uu___16 =
                                               let uu___17 =
                                                 let uu___18 =
                                                   FStarC_SMTEncoding_Term.mk_fv
                                                     (xxsym,
                                                       FStarC_SMTEncoding_Term.Term_sort) in
                                                 uu___18 :: univ_vars in
                                               FStarC_List.op_At uu___17 vars in
                                             FStarC_SMTEncoding_Env.add_fuel
                                               uu___15 uu___16 in
                                           let uu___15 =
                                             FStarC_SMTEncoding_Util.mkImp
                                               (xx_has_type_sfuel, data_ax) in
                                           ([[xx_has_type_sfuel]], uu___14,
                                             uu___15) in
                                         FStarC_SMTEncoding_Term.mkForall
                                           uu___12 uu___13 in
                                       let uu___12 =
                                         let uu___13 =
                                           let uu___14 =
                                             FStarC_Ident.string_of_lid t in
                                           Prims.strcat
                                             "fuel_guarded_inversion_"
                                             uu___14 in
                                         FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.mk_unique
                                           uu___13 in
                                       (uu___11,
                                         (FStar_Pervasives_Native.Some
                                            "inversion axiom"), uu___12) in
                                     FStarC_SMTEncoding_Util.mkAssume uu___10 in
                                   let uu___10 =
                                     FStarC_SMTEncoding_Term.mk_decls_trivial
                                       [fuel_guarded_inversion] in
                                   FStarC_List.op_At decls uu___10))) in
                let uu___5 =
                  let k2 =
                    match tps1 with
                    | [] -> k1
                    | uu___6 ->
                        let uu___7 =
                          let uu___8 =
                            let uu___9 = FStarC_Syntax_Syntax.mk_Total k1 in
                            {
                              FStarC_Syntax_Syntax.bs1 = tps1;
                              FStarC_Syntax_Syntax.comp = uu___9
                            } in
                          FStarC_Syntax_Syntax.Tm_arrow uu___8 in
                        FStarC_Syntax_Syntax.mk uu___7
                          k1.FStarC_Syntax_Syntax.pos in
                  let k3 = norm_before_encoding env1 k2 in
                  FStarC_Syntax_Util.arrow_formals k3 in
                (match uu___5 with
                 | (formals, res) ->
                     let uu___6 =
                       FStarC_SMTEncoding_EncodeTerm.encode_binders
                         FStar_Pervasives_Native.None formals env1 in
                     (match uu___6 with
                      | (vars, guards, env', binder_decls, uu___7) ->
                          let arity = FStarC_List.length vars in
                          let univ_arity1 = FStarC_List.length univ_terms in
                          let uu___8 =
                            FStarC_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                              env1 t arity univ_arity1 in
                          (match uu___8 with
                           | (tname, ttok, env2) ->
                               let ttok_tm =
                                 FStarC_SMTEncoding_Util.mkApp
                                   (ttok, univ_terms) in
                               let guard =
                                 FStarC_SMTEncoding_Util.mk_and_l guards in
                               let tapp =
                                 let uu___9 =
                                   let uu___10 =
                                     FStarC_List.map
                                       FStarC_SMTEncoding_Util.mkFreeV
                                       (FStarC_List.op_At univ_vars vars) in
                                   (tname, uu___10) in
                                 FStarC_SMTEncoding_Util.mkApp uu___9 in
                               let uu___9 =
                                 let tname_decl =
                                   let uu___10 =
                                     let uu___11 =
                                       FStarC_List.map
                                         (fun fv ->
                                            let uu___12 =
                                              let uu___13 =
                                                FStarC_SMTEncoding_Term.fv_name
                                                  fv in
                                              Prims.strcat tname uu___13 in
                                            let uu___13 =
                                              FStarC_SMTEncoding_Term.fv_sort
                                                fv in
                                            {
                                              FStarC_SMTEncoding_Term.field_name
                                                = uu___12;
                                              FStarC_SMTEncoding_Term.field_sort
                                                = uu___13;
                                              FStarC_SMTEncoding_Term.field_projectible
                                                = false
                                            })
                                         (FStarC_List.op_At univ_vars vars) in
                                     let uu___12 =
                                       let uu___13 =
                                         FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.next_id
                                           () in
                                       FStar_Pervasives_Native.Some uu___13 in
                                     {
                                       FStarC_SMTEncoding_Term.constr_name =
                                         tname;
                                       FStarC_SMTEncoding_Term.constr_fields
                                         = uu___11;
                                       FStarC_SMTEncoding_Term.constr_sort =
                                         FStarC_SMTEncoding_Term.Term_sort;
                                       FStarC_SMTEncoding_Term.constr_id =
                                         uu___12;
                                       FStarC_SMTEncoding_Term.constr_base =
                                         false
                                     } in
                                   constructor_or_logic_type_decl uu___10 in
                                 let uu___10 =
                                   match vars with
                                   | [] ->
                                       let uu___11 =
                                         let uu___12 =
                                           let uu___13 =
                                             FStarC_SMTEncoding_Util.mkApp
                                               (tname, []) in
                                           FStar_Pervasives_Native.Some
                                             uu___13 in
                                         FStarC_SMTEncoding_Env.push_free_var
                                           env2 t arity univ_arity1 tname
                                           uu___12 in
                                       ([], uu___11)
                                   | uu___11 ->
                                       let ttok_decl =
                                         let uu___12 =
                                           let uu___13 =
                                             FStarC_List.map
                                               FStarC_SMTEncoding_Term.fv_sort
                                               univ_vars in
                                           (ttok, uu___13,
                                             FStarC_SMTEncoding_Term.Term_sort,
                                             (FStar_Pervasives_Native.Some
                                                "token")) in
                                         FStarC_SMTEncoding_Term.DeclFun
                                           uu___12 in
                                       let ttok_fresh =
                                         let uu___12 =
                                           FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.next_id
                                             () in
                                         FStarC_SMTEncoding_Term.fresh_token
                                           (ttok_tm, univ_vars,
                                             FStarC_SMTEncoding_Term.Term_sort)
                                           uu___12 in
                                       let ttok_app =
                                         FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                           ttok_tm vars in
                                       let pats = [[ttok_app]; [tapp]] in
                                       let name_tok_corr =
                                         let uu___12 =
                                           let uu___13 =
                                             let uu___14 =
                                               FStarC_Ident.range_of_lid t in
                                             let uu___15 =
                                               let uu___16 =
                                                 FStarC_SMTEncoding_Util.mkEq
                                                   (ttok_app, tapp) in
                                               (pats,
                                                 FStar_Pervasives_Native.None,
                                                 (FStarC_List.op_At univ_vars
                                                    vars), uu___16) in
                                             FStarC_SMTEncoding_Term.mkForall'
                                               uu___14 uu___15 in
                                           (uu___13,
                                             (FStar_Pervasives_Native.Some
                                                "name-token correspondence"),
                                             (Prims.strcat
                                                "token_correspondence_" ttok)) in
                                         FStarC_SMTEncoding_Util.mkAssume
                                           uu___12 in
                                       ([ttok_decl;
                                        ttok_fresh;
                                        name_tok_corr], env2) in
                                 match uu___10 with
                                 | (tok_decls, env3) ->
                                     ((FStarC_List.op_At tname_decl tok_decls),
                                       env3) in
                               (match uu___9 with
                                | (decls, env3) ->
                                    let kindingAx =
                                      let uu___10 =
                                        FStarC_SMTEncoding_EncodeTerm.encode_term_pred
                                          FStar_Pervasives_Native.None res
                                          env' tapp in
                                      match uu___10 with
                                      | (k2, decls1) ->
                                          let karr =
                                            if
                                              (FStarC_List.length formals) >
                                                Prims.int_zero
                                            then
                                              let uu___11 =
                                                let uu___12 =
                                                  let uu___13 =
                                                    let uu___14 =
                                                      FStarC_Ident.range_of_lid
                                                        t in
                                                    let uu___15 =
                                                      let uu___16 =
                                                        let uu___17 =
                                                          FStarC_SMTEncoding_Term.mk_PreType
                                                            ttok_tm in
                                                        FStarC_SMTEncoding_Term.mk_tester
                                                          "Tm_arrow" uu___17 in
                                                      ([[ttok_tm]],
                                                        univ_vars, uu___16) in
                                                    FStarC_SMTEncoding_Term.mkForall
                                                      uu___14 uu___15 in
                                                  (uu___13,
                                                    (FStar_Pervasives_Native.Some
                                                       "kinding"),
                                                    (Prims.strcat
                                                       "pre_kinding_" ttok)) in
                                                FStarC_SMTEncoding_Util.mkAssume
                                                  uu___12 in
                                              [uu___11]
                                            else [] in
                                          let rng =
                                            FStarC_Ident.range_of_lid t in
                                          let tot_fun_axioms =
                                            let uu___11 =
                                              FStarC_List.map
                                                (fun uu___12 ->
                                                   FStarC_SMTEncoding_Util.mkTrue)
                                                vars in
                                            FStarC_SMTEncoding_EncodeTerm.isTotFun_axioms
                                              rng ttok_tm univ_vars vars
                                              uu___11 true in
                                          let uu___11 =
                                            let uu___12 =
                                              let uu___13 =
                                                let uu___14 =
                                                  let uu___15 =
                                                    let uu___16 =
                                                      let uu___17 =
                                                        let uu___18 =
                                                          let uu___19 =
                                                            let uu___20 =
                                                              FStarC_SMTEncoding_Util.mkImp
                                                                (guard, k2) in
                                                            ([[tapp]],
                                                              (FStarC_List.op_At
                                                                 univ_vars
                                                                 vars),
                                                              uu___20) in
                                                          FStarC_SMTEncoding_Term.mkForall
                                                            rng uu___19 in
                                                        (tot_fun_axioms,
                                                          uu___18) in
                                                      FStarC_SMTEncoding_Util.mkAnd
                                                        uu___17 in
                                                    (uu___16,
                                                      FStar_Pervasives_Native.None,
                                                      (Prims.strcat
                                                         "kinding_" ttok)) in
                                                  FStarC_SMTEncoding_Util.mkAssume
                                                    uu___15 in
                                                [uu___14] in
                                              FStarC_List.op_At karr uu___13 in
                                            FStarC_SMTEncoding_Term.mk_decls_trivial
                                              uu___12 in
                                          FStarC_List.op_At decls1 uu___11 in
                                    let aux =
                                      let uu___10 =
                                        let uu___11 =
                                          inversion_axioms env3 tapp vars in
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              let uu___15 =
                                                FStarC_Ident.range_of_lid t in
                                              pretype_axiom
                                                (Prims.op_Negation
                                                   injective_type_params)
                                                uu___15 env3 tapp
                                                (FStarC_List.op_At univ_vars
                                                   vars) in
                                            [uu___14] in
                                          FStarC_SMTEncoding_Term.mk_decls_trivial
                                            uu___13 in
                                        FStarC_List.op_At uu___11 uu___12 in
                                      FStarC_List.op_At kindingAx uu___10 in
                                    let uu___10 =
                                      let uu___11 =
                                        FStarC_SMTEncoding_Term.mk_decls_trivial
                                          decls in
                                      FStarC_List.op_At uu___11
                                        (FStarC_List.op_At binder_decls aux) in
                                    (uu___10, env3)))))))
let encode_datacon (env : FStarC_SMTEncoding_Env.env_t)
  (se : FStarC_Syntax_Syntax.sigelt) :
  (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.env_t)=
  let uu___ = se.FStarC_Syntax_Syntax.sigel in
  match uu___ with
  | FStarC_Syntax_Syntax.Sig_datacon
      { FStarC_Syntax_Syntax.lid1 = d; FStarC_Syntax_Syntax.us1 = us;
        FStarC_Syntax_Syntax.t1 = t; FStarC_Syntax_Syntax.ty_lid = uu___1;
        FStarC_Syntax_Syntax.num_ty_params = n_tps;
        FStarC_Syntax_Syntax.mutuals1 = mutuals;
        FStarC_Syntax_Syntax.injective_type_params1 = injective_type_params;
        FStarC_Syntax_Syntax.proj_disc_lids = uu___2;_}
      ->
      let quals = se.FStarC_Syntax_Syntax.sigquals in
      let uu___3 = FStarC_Syntax_Subst.open_univ_vars us t in
      (match uu___3 with
       | (us1, t1) ->
           let env1 =
             let uu___4 =
               FStarC_TypeChecker_Env.push_univ_vars
                 env.FStarC_SMTEncoding_Env.tcenv us1 in
             {
               FStarC_SMTEncoding_Env.bvar_bindings =
                 (env.FStarC_SMTEncoding_Env.bvar_bindings);
               FStarC_SMTEncoding_Env.fvar_bindings =
                 (env.FStarC_SMTEncoding_Env.fvar_bindings);
               FStarC_SMTEncoding_Env.depth =
                 (env.FStarC_SMTEncoding_Env.depth);
               FStarC_SMTEncoding_Env.tcenv = uu___4;
               FStarC_SMTEncoding_Env.warn =
                 (env.FStarC_SMTEncoding_Env.warn);
               FStarC_SMTEncoding_Env.nolabels =
                 (env.FStarC_SMTEncoding_Env.nolabels);
               FStarC_SMTEncoding_Env.use_zfuel_name =
                 (env.FStarC_SMTEncoding_Env.use_zfuel_name);
               FStarC_SMTEncoding_Env.encode_non_total_function_typ =
                 (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
               FStarC_SMTEncoding_Env.current_module_name =
                 (env.FStarC_SMTEncoding_Env.current_module_name);
               FStarC_SMTEncoding_Env.encoding_quantifier =
                 (env.FStarC_SMTEncoding_Env.encoding_quantifier);
               FStarC_SMTEncoding_Env.global_cache =
                 (env.FStarC_SMTEncoding_Env.global_cache)
             } in
           let uu___4 =
             let uu___5 =
               FStarC_List.map FStarC_SMTEncoding_EncodeTerm.encode_univ_name
                 us1 in
             FStarC_List.unzip uu___5 in
           (match uu___4 with
            | (univ_fvs, univs) ->
                let univ_sorts =
                  FStarC_List.map
                    (fun uu___5 -> FStarC_SMTEncoding_Term.univ_sort) univs in
                let t2 = norm_before_encoding env1 t1 in
                let uu___5 = FStarC_Syntax_Util.arrow_formals t2 in
                (match uu___5 with
                 | (formals, t_res) ->
                     let arity = FStarC_List.length formals in
                     let univ_arity = FStarC_List.length univs in
                     let uu___6 =
                       FStarC_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                         env1 d arity univ_arity in
                     (match uu___6 with
                      | (ddconstrsym, ddtok, env2) ->
                          let ddtok_tm =
                            FStarC_SMTEncoding_Util.mkApp (ddtok, univs) in
                          let uu___7 =
                            FStarC_SMTEncoding_Env.fresh_fvar
                              env2.FStarC_SMTEncoding_Env.current_module_name
                              "f" FStarC_SMTEncoding_Term.Fuel_sort in
                          (match uu___7 with
                           | (fuel_var, fuel_tm) ->
                               let s_fuel_tm =
                                 FStarC_SMTEncoding_Util.mkApp
                                   ("SFuel", [fuel_tm]) in
                               let uu___8 =
                                 FStarC_SMTEncoding_EncodeTerm.encode_binders
                                   (FStar_Pervasives_Native.Some fuel_tm)
                                   formals env2 in
                               (match uu___8 with
                                | (vars, guards, env', binder_decls, names)
                                    ->
                                    let injective_type_params1 =
                                      injective_type_params ||
                                        (FStarC_Options_Ext.enabled
                                           "compat:injectivity") in
                                    let univ_fields =
                                      FStarC_List.mapi
                                        (fun i uu___9 ->
                                           let uu___10 =
                                             FStarC_SMTEncoding_Env.mk_univ_projector_name
                                               d i in
                                           {
                                             FStarC_SMTEncoding_Term.field_name
                                               = uu___10;
                                             FStarC_SMTEncoding_Term.field_sort
                                               =
                                               FStarC_SMTEncoding_Term.univ_sort;
                                             FStarC_SMTEncoding_Term.field_projectible
                                               = true
                                           }) univs in
                                    let n_univs =
                                      FStarC_List.length univ_fields in
                                    let fields =
                                      FStarC_List.mapi
                                        (fun n x ->
                                           let field_projectible =
                                             (n >= n_tps) ||
                                               injective_type_params1 in
                                           let uu___9 =
                                             FStarC_SMTEncoding_Env.mk_term_projector_name
                                               d x in
                                           {
                                             FStarC_SMTEncoding_Term.field_name
                                               = uu___9;
                                             FStarC_SMTEncoding_Term.field_sort
                                               =
                                               FStarC_SMTEncoding_Term.Term_sort;
                                             FStarC_SMTEncoding_Term.field_projectible
                                               = field_projectible
                                           }) names in
                                    let datacons =
                                      let uu___9 =
                                        FStarC_Ident.range_of_lid d in
                                      let uu___10 =
                                        let uu___11 =
                                          let uu___12 =
                                            FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.next_id
                                              () in
                                          FStar_Pervasives_Native.Some
                                            uu___12 in
                                        {
                                          FStarC_SMTEncoding_Term.constr_name
                                            = ddconstrsym;
                                          FStarC_SMTEncoding_Term.constr_fields
                                            =
                                            (FStarC_List.op_At univ_fields
                                               fields);
                                          FStarC_SMTEncoding_Term.constr_sort
                                            =
                                            FStarC_SMTEncoding_Term.Term_sort;
                                          FStarC_SMTEncoding_Term.constr_id =
                                            uu___11;
                                          FStarC_SMTEncoding_Term.constr_base
                                            =
                                            (Prims.op_Negation
                                               injective_type_params1)
                                        } in
                                      FStarC_SMTEncoding_Term.constructor_to_decl
                                        uu___9 uu___10 in
                                    let app =
                                      FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                        ddtok_tm vars in
                                    let guard =
                                      FStarC_SMTEncoding_Util.mk_and_l guards in
                                    let xvars =
                                      FStarC_List.map
                                        FStarC_SMTEncoding_Util.mkFreeV vars in
                                    let dapp =
                                      FStarC_SMTEncoding_Util.mkApp
                                        (ddconstrsym,
                                          (FStarC_List.op_At univs xvars)) in
                                    let uu___9 =
                                      FStarC_SMTEncoding_EncodeTerm.encode_term_pred
                                        FStar_Pervasives_Native.None t2 env2
                                        ddtok_tm in
                                    (match uu___9 with
                                     | (tok_typing, decls3) ->
                                         let tok_typing1 =
                                           match (fields, univs) with
                                           | (uu___10::uu___11, []) ->
                                               let ff =
                                                 FStarC_SMTEncoding_Term.mk_fv
                                                   ("ty",
                                                     FStarC_SMTEncoding_Term.Term_sort) in
                                               let f =
                                                 FStarC_SMTEncoding_Util.mkFreeV
                                                   ff in
                                               let vtok_app_l =
                                                 FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                                   ddtok_tm [ff] in
                                               let vtok_app_r =
                                                 let uu___12 =
                                                   let uu___13 =
                                                     FStarC_SMTEncoding_Term.mk_fv
                                                       (ddtok,
                                                         FStarC_SMTEncoding_Term.Term_sort) in
                                                   [uu___13] in
                                                 FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                                   f uu___12 in
                                               let uu___12 =
                                                 FStarC_Ident.range_of_lid d in
                                               let uu___13 =
                                                 let uu___14 =
                                                   FStarC_SMTEncoding_Term.mk_NoHoist
                                                     f tok_typing in
                                                 ([[vtok_app_l];
                                                  [vtok_app_r]], [ff],
                                                   uu___14) in
                                               FStarC_SMTEncoding_Term.mkForall
                                                 uu___12 uu___13
                                           | uu___10 ->
                                               let uu___11 =
                                                 FStarC_Ident.range_of_lid d in
                                               close_universes uu___11
                                                 univ_fvs ddtok_tm tok_typing in
                                         let uu___10 =
                                           let uu___11 =
                                             FStarC_SMTEncoding_EncodeTerm.encode_term
                                               t_res env' in
                                           match uu___11 with
                                           | (t_res_tm, t_res_decls) ->
                                               let uu___12 =
                                                 FStarC_SMTEncoding_Term.mk_HasTypeWithFuel
                                                   (FStar_Pervasives_Native.Some
                                                      fuel_tm) dapp t_res_tm in
                                               (uu___12, t_res_tm,
                                                 t_res_decls) in
                                         (match uu___10 with
                                          | (ty_pred', t_res_tm, decls_pred)
                                              ->
                                              let proxy_fresh =
                                                match formals with
                                                | [] -> []
                                                | uu___11 ->
                                                    let uu___12 =
                                                      let uu___13 =
                                                        FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.next_id
                                                          () in
                                                      FStarC_SMTEncoding_Term.fresh_token
                                                        (ddtok_tm, univ_fvs,
                                                          FStarC_SMTEncoding_Term.Term_sort)
                                                        uu___13 in
                                                    [uu___12] in
                                              let encode_elim uu___11 =
                                                let uu___12 =
                                                  FStarC_Syntax_Util.head_and_args
                                                    t_res in
                                                match uu___12 with
                                                | (head, args) ->
                                                    let uu___13 =
                                                      let uu___14 =
                                                        FStarC_Syntax_Subst.compress
                                                          head in
                                                      uu___14.FStarC_Syntax_Syntax.n in
                                                    (match uu___13 with
                                                     | FStarC_Syntax_Syntax.Tm_uinst
                                                         ({
                                                            FStarC_Syntax_Syntax.n
                                                              =
                                                              FStarC_Syntax_Syntax.Tm_fvar
                                                              fv;
                                                            FStarC_Syntax_Syntax.pos
                                                              = uu___14;
                                                            FStarC_Syntax_Syntax.vars
                                                              = uu___15;
                                                            FStarC_Syntax_Syntax.hash_code
                                                              = uu___16;_},
                                                          uu___17)
                                                         ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStarC_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStarC_Syntax_Syntax.fv_name in
                                                         let uu___18 =
                                                           FStarC_SMTEncoding_EncodeTerm.encode_args
                                                             args env' in
                                                         (match uu___18 with
                                                          | (encoded_args,
                                                             arg_decls) ->
                                                              let uu___19 =
                                                                let uu___20 =
                                                                  FStarC_List.zip
                                                                    args
                                                                    encoded_args in
                                                                FStarC_List.fold_left
                                                                  (fun
                                                                    uu___21
                                                                    uu___22
                                                                    ->
                                                                    match 
                                                                    (uu___21,
                                                                    uu___22)
                                                                    with
                                                                    | 
                                                                    ((env3,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStarC_Syntax_Syntax.tun in
                                                                    FStarC_SMTEncoding_Env.gen_term_var
                                                                    env3
                                                                    uu___24 in
                                                                    (match uu___23
                                                                    with
                                                                    | 
                                                                    (uu___24,
                                                                    xv, env4)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu___26
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu___26
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env4,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    Prims.int_one))))
                                                                  (env', [],
                                                                    [],
                                                                    Prims.int_zero)
                                                                  uu___20 in
                                                              (match uu___19
                                                               with
                                                               | (uu___20,
                                                                  arg_vars,
                                                                  elim_eqns_or_guards,
                                                                  uu___21) ->
                                                                   let arg_vars1
                                                                    =
                                                                    FStarC_List.rev
                                                                    arg_vars in
                                                                   let uu___22
                                                                    =
                                                                    FStarC_List.splitAt
                                                                    n_tps
                                                                    arg_vars1 in
                                                                   (match uu___22
                                                                    with
                                                                    | 
                                                                    (arg_params,
                                                                    uu___23)
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    FStarC_List.splitAt
                                                                    n_tps
                                                                    vars in
                                                                    (match uu___24
                                                                    with
                                                                    | 
                                                                    (data_arg_params,
                                                                    uu___25)
                                                                    ->
                                                                    let elim_eqns_and_guards
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    (FStarC_List.op_At
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    FStarC_List.fold_left2
                                                                    (fun
                                                                    elim_eqns_and_guards1
                                                                    data_arg_param
                                                                    arg_param
                                                                    ->
                                                                    FStarC_SMTEncoding_Term.subst
                                                                    elim_eqns_and_guards1
                                                                    data_arg_param
                                                                    arg_param)
                                                                    uu___26
                                                                    data_arg_params
                                                                    arg_params in
                                                                    let ty =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Class_HasRange.pos
                                                                    FStarC_Ident.hasrange_lident
                                                                    fv.FStarC_Syntax_Syntax.fv_name in
                                                                    FStarC_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    uu___26
                                                                    {
                                                                    FStarC_SMTEncoding_Env.fvar_lid
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.fvar_lid);
                                                                    FStarC_SMTEncoding_Env.univ_arity
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.univ_arity);
                                                                    FStarC_SMTEncoding_Env.smt_arity
                                                                    =
                                                                    ((FStarC_List.length
                                                                    univs) +
                                                                    encoded_head_fvb.FStarC_SMTEncoding_Env.smt_arity);
                                                                    FStarC_SMTEncoding_Env.smt_id
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.smt_id);
                                                                    FStarC_SMTEncoding_Env.smt_token
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.smt_token);
                                                                    FStarC_SMTEncoding_Env.smt_fuel_partial_app
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.smt_fuel_partial_app);
                                                                    FStarC_SMTEncoding_Env.fvb_thunked
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.fvb_thunked);
                                                                    FStarC_SMTEncoding_Env.needs_fuel_and_universe_instantiations
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.needs_fuel_and_universe_instantiations)
                                                                    }
                                                                    (FStarC_List.op_At
                                                                    univs
                                                                    arg_vars1) in
                                                                    let xvars1
                                                                    =
                                                                    FStarC_List.map
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let dapp1
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    (FStarC_List.op_At
                                                                    univs
                                                                    xvars1)) in
                                                                    let ty_pred
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                    let arg_binders
                                                                    =
                                                                    FStarC_List.map
                                                                    FStarC_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Ident.range_of_lid
                                                                    d in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStarC_SMTEncoding_Term.Fuel_sort) in
                                                                    FStarC_SMTEncoding_Env.add_fuel
                                                                    uu___31
                                                                    (FStarC_List.op_At
                                                                    univ_fvs
                                                                    (FStarC_List.op_At
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu___31
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkImp
                                                                    (ty_pred,
                                                                    elim_eqns_and_guards) in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___30,
                                                                    uu___31) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___28
                                                                    uu___29 in
                                                                    (uu___27,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___26 in
                                                                    let lex_t
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    FStarC_Parser_Const.lex_t_lid in
                                                                    (uu___28,
                                                                    FStarC_SMTEncoding_Term.Term_sort) in
                                                                    FStarC_SMTEncoding_Term.mk_fv
                                                                    uu___27 in
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    uu___26 in
                                                                    let subterm_ordering
                                                                    =
                                                                    let prec
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_List.mapi
                                                                    (fun i v
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStarC_SMTEncoding_Util.mk_Precedes
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    lex_t
                                                                    lex_t
                                                                    uu___29
                                                                    dapp1 in
                                                                    [uu___28]))
                                                                    vars in
                                                                    FStarC_List.flatten
                                                                    uu___26 in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStarC_Ident.range_of_lid
                                                                    d in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStarC_SMTEncoding_Term.Fuel_sort) in
                                                                    FStarC_SMTEncoding_Env.add_fuel
                                                                    uu___31
                                                                    (FStarC_List.op_At
                                                                    univ_fvs
                                                                    (FStarC_List.op_At
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu___33) in
                                                                    FStarC_SMTEncoding_Util.mkImp
                                                                    uu___32 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___30,
                                                                    uu___31) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___28
                                                                    uu___29 in
                                                                    (uu___27,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___26 in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_Util.first_N
                                                                    n_tps
                                                                    formals in
                                                                    match uu___27
                                                                    with
                                                                    | 
                                                                    (uu___28,
                                                                    formals')
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Util.first_N
                                                                    n_tps
                                                                    vars in
                                                                    (match uu___29
                                                                    with
                                                                    | 
                                                                    (uu___30,
                                                                    vars') ->
                                                                    let norm
                                                                    t3 =
                                                                    FStarC_TypeChecker_Normalize.unfold_whnf'
                                                                    [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                                                                    FStarC_TypeChecker_Env.Unascribe;
                                                                    FStarC_TypeChecker_Env.Exclude
                                                                    FStarC_TypeChecker_Env.Zeta]
                                                                    env'.FStarC_SMTEncoding_Env.tcenv
                                                                    t3 in
                                                                    let warn_compat
                                                                    uu___31 =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Errors_Msg.text
                                                                    "Using 'compat:2954' to use a permissive encoding of the subterm ordering on the codomain of a constructor." in
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStarC_Errors_Msg.text
                                                                    "This is deprecated and will be removed in a future version of F*." in
                                                                    [uu___35] in
                                                                    uu___33
                                                                    ::
                                                                    uu___34 in
                                                                    FStarC_Errors.log_issue
                                                                    FStarC_Syntax_Syntax.hasRange_fv
                                                                    fv
                                                                    FStarC_Errors_Codes.Warning_DeprecatedGeneric
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_list_doc)
                                                                    (Obj.magic
                                                                    uu___32) in
                                                                    let uu___31
                                                                    =
                                                                    FStarC_List.fold_left2
                                                                    (fun
                                                                    uu___32
                                                                    formal
                                                                    var ->
                                                                    match uu___32
                                                                    with
                                                                    | 
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    ->
                                                                    let rec binder_and_codomain_type
                                                                    t3 =
                                                                    let t4 =
                                                                    FStarC_Syntax_Util.unrefine
                                                                    t3 in
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    t4 in
                                                                    uu___34.FStarC_Syntax_Syntax.n in
                                                                    match uu___33
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_arrow
                                                                    uu___34
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStarC_Syntax_Util.unrefine
                                                                    t4 in
                                                                    FStarC_Syntax_Util.arrow_formals_comp
                                                                    uu___36 in
                                                                    (match uu___35
                                                                    with
                                                                    | 
                                                                    (bs, c)
                                                                    ->
                                                                    (match bs
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu___36
                                                                    when
                                                                    let uu___37
                                                                    =
                                                                    FStarC_Syntax_Util.is_tot_or_gtot_comp
                                                                    c in
                                                                    Prims.op_Negation
                                                                    uu___37
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu___36
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    FStarC_Syntax_Util.is_lemma_comp
                                                                    c in
                                                                    if
                                                                    uu___37
                                                                    then
                                                                    FStar_Pervasives_Native.None
                                                                    else
                                                                    (let t5 =
                                                                    let uu___39
                                                                    =
                                                                    FStarC_Syntax_Util.comp_result
                                                                    c in
                                                                    FStarC_Syntax_Util.unrefine
                                                                    uu___39 in
                                                                    let t6 =
                                                                    norm t5 in
                                                                    let uu___39
                                                                    =
                                                                    (FStarC_Syntax_Syntax.is_type
                                                                    t6) ||
                                                                    (FStarC_Syntax_Util.is_sub_singleton
                                                                    t6) in
                                                                    if
                                                                    uu___39
                                                                    then
                                                                    FStar_Pervasives_Native.None
                                                                    else
                                                                    (let uu___41
                                                                    =
                                                                    FStarC_Syntax_Util.head_and_args_full
                                                                    t6 in
                                                                    match uu___41
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___42)
                                                                    ->
                                                                    let uu___43
                                                                    =
                                                                    let uu___44
                                                                    =
                                                                    FStarC_Syntax_Util.un_uinst
                                                                    head1 in
                                                                    uu___44.FStarC_Syntax_Syntax.n in
                                                                    (match uu___43
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_fvar
                                                                    fv1 ->
                                                                    let uu___44
                                                                    =
                                                                    FStarC_Util.for_some
                                                                    (FStarC_Syntax_Syntax.fv_eq_lid
                                                                    fv1)
                                                                    mutuals in
                                                                    if
                                                                    uu___44
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    (bs, c)
                                                                    else
                                                                    (let uu___46
                                                                    =
                                                                    FStarC_Options_Ext.enabled
                                                                    "compat:2954" in
                                                                    if
                                                                    uu___46
                                                                    then
                                                                    (warn_compat
                                                                    ();
                                                                    FStar_Pervasives_Native.Some
                                                                    (bs, c))
                                                                    else
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    uu___44
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    FStarC_Options_Ext.enabled
                                                                    "compat:2954" in
                                                                    if
                                                                    uu___45
                                                                    then
                                                                    (warn_compat
                                                                    ();
                                                                    FStar_Pervasives_Native.Some
                                                                    (bs, c))
                                                                    else
                                                                    FStar_Pervasives_Native.None)))))
                                                                    | 
                                                                    uu___34
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_Syntax_Util.head_and_args
                                                                    t4 in
                                                                    (match uu___35
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___36)
                                                                    ->
                                                                    let t' =
                                                                    norm t4 in
                                                                    let uu___37
                                                                    =
                                                                    FStarC_Syntax_Util.head_and_args
                                                                    t' in
                                                                    (match uu___37
                                                                    with
                                                                    | 
                                                                    (head',
                                                                    uu___38)
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                                    env2.FStarC_SMTEncoding_Env.tcenv
                                                                    head1
                                                                    head' in
                                                                    (match uu___39
                                                                    with
                                                                    | 
                                                                    FStarC_TypeChecker_TermEqAndSimplify.Equal
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStarC_TypeChecker_TermEqAndSimplify.NotEqual
                                                                    ->
                                                                    binder_and_codomain_type
                                                                    t'
                                                                    | 
                                                                    uu___40
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    head1 in
                                                                    uu___42.FStarC_Syntax_Syntax.n in
                                                                    (match uu___41
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_fvar
                                                                    uu___42
                                                                    ->
                                                                    binder_and_codomain_type
                                                                    t'
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_name
                                                                    uu___42
                                                                    ->
                                                                    binder_and_codomain_type
                                                                    t'
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_uinst
                                                                    uu___42
                                                                    ->
                                                                    binder_and_codomain_type
                                                                    t'
                                                                    | 
                                                                    uu___42
                                                                    ->
                                                                    FStar_Pervasives_Native.None)))) in
                                                                    let uu___33
                                                                    =
                                                                    binder_and_codomain_type
                                                                    (formal.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    (match uu___33
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (bs, c)
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStarC_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    bs env' in
                                                                    (match uu___34
                                                                    with
                                                                    | 
                                                                    (bs',
                                                                    guards',
                                                                    _env',
                                                                    bs_decls,
                                                                    uu___35)
                                                                    ->
                                                                    let fun_app
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    var in
                                                                    FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu___36
                                                                    bs' in
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStarC_Ident.range_of_lid
                                                                    d in
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_Precedes
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    lex_t
                                                                    lex_t
                                                                    fun_app
                                                                    dapp1 in
                                                                    [uu___42] in
                                                                    [uu___41] in
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    let uu___43
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    (ty_pred'
                                                                    ::
                                                                    guards') in
                                                                    let uu___44
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_Precedes
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    lex_t
                                                                    lex_t
                                                                    fun_app
                                                                    dapp1 in
                                                                    (uu___43,
                                                                    uu___44) in
                                                                    FStarC_SMTEncoding_Util.mkImp
                                                                    uu___42 in
                                                                    (uu___40,
                                                                    bs',
                                                                    uu___41) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___38
                                                                    uu___39 in
                                                                    uu___37
                                                                    ::
                                                                    codomain_prec_l in
                                                                    (uu___36,
                                                                    (FStarC_List.op_At
                                                                    bs_decls
                                                                    cod_decls)))))
                                                                    ([], [])
                                                                    formals'
                                                                    vars' in
                                                                    (match uu___31
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
                                                                    uu___32
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    FStarC_Ident.range_of_lid
                                                                    d in
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStarC_SMTEncoding_Term.Fuel_sort) in
                                                                    FStarC_SMTEncoding_Env.add_fuel
                                                                    uu___40
                                                                    (FStarC_List.op_At
                                                                    univ_fvs
                                                                    (FStarC_List.op_At
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu___40
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    codomain_prec_l in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___39,
                                                                    uu___40) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___37
                                                                    uu___38 in
                                                                    (uu___36,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "well-founded ordering on codomain"),
                                                                    (Prims.strcat
                                                                    "well_founded_ordering_on_codomain_"
                                                                    ddconstrsym)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___35 in
                                                                    [uu___34] in
                                                                    (uu___33,
                                                                    cod_decls)))) in
                                                                    (match uu___26
                                                                    with
                                                                    | 
                                                                    (codomain_ordering,
                                                                    codomain_decls)
                                                                    ->
                                                                    ((FStarC_List.op_At
                                                                    arg_decls
                                                                    codomain_decls),
                                                                    (FStarC_List.op_At
                                                                    [typing_inversion;
                                                                    subterm_ordering]
                                                                    codomain_ordering)))))))
                                                     | FStarC_Syntax_Syntax.Tm_fvar
                                                         fv ->
                                                         let encoded_head_fvb
                                                           =
                                                           FStarC_SMTEncoding_Env.lookup_free_var_name
                                                             env'
                                                             fv.FStarC_Syntax_Syntax.fv_name in
                                                         let uu___14 =
                                                           FStarC_SMTEncoding_EncodeTerm.encode_args
                                                             args env' in
                                                         (match uu___14 with
                                                          | (encoded_args,
                                                             arg_decls) ->
                                                              let uu___15 =
                                                                let uu___16 =
                                                                  FStarC_List.zip
                                                                    args
                                                                    encoded_args in
                                                                FStarC_List.fold_left
                                                                  (fun
                                                                    uu___17
                                                                    uu___18
                                                                    ->
                                                                    match 
                                                                    (uu___17,
                                                                    uu___18)
                                                                    with
                                                                    | 
                                                                    ((env3,
                                                                    arg_vars,
                                                                    eqns_or_guards,
                                                                    i),
                                                                    (orig_arg,
                                                                    arg)) ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStarC_Syntax_Syntax.tun in
                                                                    FStarC_SMTEncoding_Env.gen_term_var
                                                                    env3
                                                                    uu___20 in
                                                                    (match uu___19
                                                                    with
                                                                    | 
                                                                    (uu___20,
                                                                    xv, env4)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu___22
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu___22
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env4,
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
                                                                    FStarC_List.rev
                                                                    arg_vars in
                                                                   let uu___18
                                                                    =
                                                                    FStarC_List.splitAt
                                                                    n_tps
                                                                    arg_vars1 in
                                                                   (match uu___18
                                                                    with
                                                                    | 
                                                                    (arg_params,
                                                                    uu___19)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStarC_List.splitAt
                                                                    n_tps
                                                                    vars in
                                                                    (match uu___20
                                                                    with
                                                                    | 
                                                                    (data_arg_params,
                                                                    uu___21)
                                                                    ->
                                                                    let elim_eqns_and_guards
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    (FStarC_List.op_At
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    FStarC_List.fold_left2
                                                                    (fun
                                                                    elim_eqns_and_guards1
                                                                    data_arg_param
                                                                    arg_param
                                                                    ->
                                                                    FStarC_SMTEncoding_Term.subst
                                                                    elim_eqns_and_guards1
                                                                    data_arg_param
                                                                    arg_param)
                                                                    uu___22
                                                                    data_arg_params
                                                                    arg_params in
                                                                    let ty =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Class_HasRange.pos
                                                                    FStarC_Ident.hasrange_lident
                                                                    fv.FStarC_Syntax_Syntax.fv_name in
                                                                    FStarC_SMTEncoding_EncodeTerm.maybe_curry_fvb
                                                                    uu___22
                                                                    {
                                                                    FStarC_SMTEncoding_Env.fvar_lid
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.fvar_lid);
                                                                    FStarC_SMTEncoding_Env.univ_arity
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.univ_arity);
                                                                    FStarC_SMTEncoding_Env.smt_arity
                                                                    =
                                                                    ((FStarC_List.length
                                                                    univs) +
                                                                    encoded_head_fvb.FStarC_SMTEncoding_Env.smt_arity);
                                                                    FStarC_SMTEncoding_Env.smt_id
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.smt_id);
                                                                    FStarC_SMTEncoding_Env.smt_token
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.smt_token);
                                                                    FStarC_SMTEncoding_Env.smt_fuel_partial_app
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.smt_fuel_partial_app);
                                                                    FStarC_SMTEncoding_Env.fvb_thunked
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.fvb_thunked);
                                                                    FStarC_SMTEncoding_Env.needs_fuel_and_universe_instantiations
                                                                    =
                                                                    (encoded_head_fvb.FStarC_SMTEncoding_Env.needs_fuel_and_universe_instantiations)
                                                                    }
                                                                    (FStarC_List.op_At
                                                                    univs
                                                                    arg_vars1) in
                                                                    let xvars1
                                                                    =
                                                                    FStarC_List.map
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                    let dapp1
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    (FStarC_List.op_At
                                                                    univs
                                                                    xvars1)) in
                                                                    let ty_pred
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                    let arg_binders
                                                                    =
                                                                    FStarC_List.map
                                                                    FStarC_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                    let typing_inversion
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Ident.range_of_lid
                                                                    d in
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStarC_SMTEncoding_Term.Fuel_sort) in
                                                                    FStarC_SMTEncoding_Env.add_fuel
                                                                    uu___27
                                                                    (FStarC_List.op_At
                                                                    univ_fvs
                                                                    (FStarC_List.op_At
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu___27
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkImp
                                                                    (ty_pred,
                                                                    elim_eqns_and_guards) in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___26,
                                                                    uu___27) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___24
                                                                    uu___25 in
                                                                    (uu___23,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___22 in
                                                                    let lex_t
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Ident.string_of_lid
                                                                    FStarC_Parser_Const.lex_t_lid in
                                                                    (uu___24,
                                                                    FStarC_SMTEncoding_Term.Term_sort) in
                                                                    FStarC_SMTEncoding_Term.mk_fv
                                                                    uu___23 in
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    uu___22 in
                                                                    let subterm_ordering
                                                                    =
                                                                    let prec
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_List.mapi
                                                                    (fun i v
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    v in
                                                                    FStarC_SMTEncoding_Util.mk_Precedes
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    lex_t
                                                                    lex_t
                                                                    uu___25
                                                                    dapp1 in
                                                                    [uu___24]))
                                                                    vars in
                                                                    FStarC_List.flatten
                                                                    uu___22 in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Ident.range_of_lid
                                                                    d in
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStarC_SMTEncoding_Term.Fuel_sort) in
                                                                    FStarC_SMTEncoding_Env.add_fuel
                                                                    uu___27
                                                                    (FStarC_List.op_At
                                                                    univ_fvs
                                                                    (FStarC_List.op_At
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu___29) in
                                                                    FStarC_SMTEncoding_Util.mkImp
                                                                    uu___28 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___26,
                                                                    uu___27) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___24
                                                                    uu___25 in
                                                                    (uu___23,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___22 in
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Util.first_N
                                                                    n_tps
                                                                    formals in
                                                                    match uu___23
                                                                    with
                                                                    | 
                                                                    (uu___24,
                                                                    formals')
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    FStarC_Util.first_N
                                                                    n_tps
                                                                    vars in
                                                                    (match uu___25
                                                                    with
                                                                    | 
                                                                    (uu___26,
                                                                    vars') ->
                                                                    let norm
                                                                    t3 =
                                                                    FStarC_TypeChecker_Normalize.unfold_whnf'
                                                                    [FStarC_TypeChecker_Env.AllowUnboundUniverses;
                                                                    FStarC_TypeChecker_Env.Unascribe;
                                                                    FStarC_TypeChecker_Env.Exclude
                                                                    FStarC_TypeChecker_Env.Zeta]
                                                                    env'.FStarC_SMTEncoding_Env.tcenv
                                                                    t3 in
                                                                    let warn_compat
                                                                    uu___27 =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Errors_Msg.text
                                                                    "Using 'compat:2954' to use a permissive encoding of the subterm ordering on the codomain of a constructor." in
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    FStarC_Errors_Msg.text
                                                                    "This is deprecated and will be removed in a future version of F*." in
                                                                    [uu___31] in
                                                                    uu___29
                                                                    ::
                                                                    uu___30 in
                                                                    FStarC_Errors.log_issue
                                                                    FStarC_Syntax_Syntax.hasRange_fv
                                                                    fv
                                                                    FStarC_Errors_Codes.Warning_DeprecatedGeneric
                                                                    ()
                                                                    (Obj.magic
                                                                    FStarC_Errors_Msg.is_error_message_list_doc)
                                                                    (Obj.magic
                                                                    uu___28) in
                                                                    let uu___27
                                                                    =
                                                                    FStarC_List.fold_left2
                                                                    (fun
                                                                    uu___28
                                                                    formal
                                                                    var ->
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    ->
                                                                    let rec binder_and_codomain_type
                                                                    t3 =
                                                                    let t4 =
                                                                    FStarC_Syntax_Util.unrefine
                                                                    t3 in
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    t4 in
                                                                    uu___30.FStarC_Syntax_Syntax.n in
                                                                    match uu___29
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_arrow
                                                                    uu___30
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    FStarC_Syntax_Util.unrefine
                                                                    t4 in
                                                                    FStarC_Syntax_Util.arrow_formals_comp
                                                                    uu___32 in
                                                                    (match uu___31
                                                                    with
                                                                    | 
                                                                    (bs, c)
                                                                    ->
                                                                    (match bs
                                                                    with
                                                                    | 
                                                                    [] ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu___32
                                                                    when
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Syntax_Util.is_tot_or_gtot_comp
                                                                    c in
                                                                    Prims.op_Negation
                                                                    uu___33
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu___32
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Syntax_Util.is_lemma_comp
                                                                    c in
                                                                    if
                                                                    uu___33
                                                                    then
                                                                    FStar_Pervasives_Native.None
                                                                    else
                                                                    (let t5 =
                                                                    let uu___35
                                                                    =
                                                                    FStarC_Syntax_Util.comp_result
                                                                    c in
                                                                    FStarC_Syntax_Util.unrefine
                                                                    uu___35 in
                                                                    let t6 =
                                                                    norm t5 in
                                                                    let uu___35
                                                                    =
                                                                    (FStarC_Syntax_Syntax.is_type
                                                                    t6) ||
                                                                    (FStarC_Syntax_Util.is_sub_singleton
                                                                    t6) in
                                                                    if
                                                                    uu___35
                                                                    then
                                                                    FStar_Pervasives_Native.None
                                                                    else
                                                                    (let uu___37
                                                                    =
                                                                    FStarC_Syntax_Util.head_and_args_full
                                                                    t6 in
                                                                    match uu___37
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___38)
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStarC_Syntax_Util.un_uinst
                                                                    head1 in
                                                                    uu___40.FStarC_Syntax_Syntax.n in
                                                                    (match uu___39
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_fvar
                                                                    fv1 ->
                                                                    let uu___40
                                                                    =
                                                                    FStarC_Util.for_some
                                                                    (FStarC_Syntax_Syntax.fv_eq_lid
                                                                    fv1)
                                                                    mutuals in
                                                                    if
                                                                    uu___40
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    (bs, c)
                                                                    else
                                                                    (let uu___42
                                                                    =
                                                                    FStarC_Options_Ext.enabled
                                                                    "compat:2954" in
                                                                    if
                                                                    uu___42
                                                                    then
                                                                    (warn_compat
                                                                    ();
                                                                    FStar_Pervasives_Native.Some
                                                                    (bs, c))
                                                                    else
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    uu___40
                                                                    ->
                                                                    let uu___41
                                                                    =
                                                                    FStarC_Options_Ext.enabled
                                                                    "compat:2954" in
                                                                    if
                                                                    uu___41
                                                                    then
                                                                    (warn_compat
                                                                    ();
                                                                    FStar_Pervasives_Native.Some
                                                                    (bs, c))
                                                                    else
                                                                    FStar_Pervasives_Native.None)))))
                                                                    | 
                                                                    uu___30
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    FStarC_Syntax_Util.head_and_args
                                                                    t4 in
                                                                    (match uu___31
                                                                    with
                                                                    | 
                                                                    (head1,
                                                                    uu___32)
                                                                    ->
                                                                    let t' =
                                                                    norm t4 in
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Syntax_Util.head_and_args
                                                                    t' in
                                                                    (match uu___33
                                                                    with
                                                                    | 
                                                                    (head',
                                                                    uu___34)
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    FStarC_TypeChecker_TermEqAndSimplify.eq_tm
                                                                    env2.FStarC_SMTEncoding_Env.tcenv
                                                                    head1
                                                                    head' in
                                                                    (match uu___35
                                                                    with
                                                                    | 
                                                                    FStarC_TypeChecker_TermEqAndSimplify.Equal
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStarC_TypeChecker_TermEqAndSimplify.NotEqual
                                                                    ->
                                                                    binder_and_codomain_type
                                                                    t'
                                                                    | 
                                                                    uu___36
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStarC_Syntax_Subst.compress
                                                                    head1 in
                                                                    uu___38.FStarC_Syntax_Syntax.n in
                                                                    (match uu___37
                                                                    with
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_fvar
                                                                    uu___38
                                                                    ->
                                                                    binder_and_codomain_type
                                                                    t'
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_name
                                                                    uu___38
                                                                    ->
                                                                    binder_and_codomain_type
                                                                    t'
                                                                    | 
                                                                    FStarC_Syntax_Syntax.Tm_uinst
                                                                    uu___38
                                                                    ->
                                                                    binder_and_codomain_type
                                                                    t'
                                                                    | 
                                                                    uu___38
                                                                    ->
                                                                    FStar_Pervasives_Native.None)))) in
                                                                    let uu___29
                                                                    =
                                                                    binder_and_codomain_type
                                                                    (formal.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                                                    (match uu___29
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (codomain_prec_l,
                                                                    cod_decls)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (bs, c)
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStarC_SMTEncoding_EncodeTerm.encode_binders
                                                                    FStar_Pervasives_Native.None
                                                                    bs env' in
                                                                    (match uu___30
                                                                    with
                                                                    | 
                                                                    (bs',
                                                                    guards',
                                                                    _env',
                                                                    bs_decls,
                                                                    uu___31)
                                                                    ->
                                                                    let fun_app
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkFreeV
                                                                    var in
                                                                    FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                                                    uu___32
                                                                    bs' in
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStarC_Ident.range_of_lid
                                                                    d in
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_Precedes
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    lex_t
                                                                    lex_t
                                                                    fun_app
                                                                    dapp1 in
                                                                    [uu___38] in
                                                                    [uu___37] in
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    (ty_pred'
                                                                    ::
                                                                    guards') in
                                                                    let uu___40
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_Precedes
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    FStarC_SMTEncoding_Term.mk_U_zero
                                                                    lex_t
                                                                    lex_t
                                                                    fun_app
                                                                    dapp1 in
                                                                    (uu___39,
                                                                    uu___40) in
                                                                    FStarC_SMTEncoding_Util.mkImp
                                                                    uu___38 in
                                                                    (uu___36,
                                                                    bs',
                                                                    uu___37) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___34
                                                                    uu___35 in
                                                                    uu___33
                                                                    ::
                                                                    codomain_prec_l in
                                                                    (uu___32,
                                                                    (FStarC_List.op_At
                                                                    bs_decls
                                                                    cod_decls)))))
                                                                    ([], [])
                                                                    formals'
                                                                    vars' in
                                                                    (match uu___27
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
                                                                    uu___28
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Ident.range_of_lid
                                                                    d in
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStarC_SMTEncoding_Term.Fuel_sort) in
                                                                    FStarC_SMTEncoding_Env.add_fuel
                                                                    uu___36
                                                                    (FStarC_List.op_At
                                                                    univ_fvs
                                                                    (FStarC_List.op_At
                                                                    vars
                                                                    arg_binders)) in
                                                                    let uu___36
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    codomain_prec_l in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu___35,
                                                                    uu___36) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___33
                                                                    uu___34 in
                                                                    (uu___32,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "well-founded ordering on codomain"),
                                                                    (Prims.strcat
                                                                    "well_founded_ordering_on_codomain_"
                                                                    ddconstrsym)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___31 in
                                                                    [uu___30] in
                                                                    (uu___29,
                                                                    cod_decls)))) in
                                                                    (match uu___22
                                                                    with
                                                                    | 
                                                                    (codomain_ordering,
                                                                    codomain_decls)
                                                                    ->
                                                                    ((FStarC_List.op_At
                                                                    arg_decls
                                                                    codomain_decls),
                                                                    (FStarC_List.op_At
                                                                    [typing_inversion;
                                                                    subterm_ordering]
                                                                    codomain_ordering)))))))
                                                     | uu___14 ->
                                                         ((let uu___16 =
                                                             let uu___17 =
                                                               FStarC_Class_Show.show
                                                                 FStarC_Ident.showable_lident
                                                                 d in
                                                             let uu___18 =
                                                               FStarC_Class_Show.show
                                                                 FStarC_Syntax_Print.showable_term
                                                                 head in
                                                             FStarC_Format.fmt2
                                                               "Constructor %s builds an unexpected type %s"
                                                               uu___17
                                                               uu___18 in
                                                           FStarC_Errors.log_issue
                                                             FStarC_Syntax_Syntax.has_range_sigelt
                                                             se
                                                             FStarC_Errors_Codes.Warning_ConstructorBuildsUnexpectedType
                                                             ()
                                                             (Obj.magic
                                                                FStarC_Errors_Msg.is_error_message_string)
                                                             (Obj.magic
                                                                uu___16));
                                                          ([], []))) in
                                              let uu___11 = encode_elim () in
                                              (match uu___11 with
                                               | (decls2, elim) ->
                                                   let data_cons_typing_intro_decl
                                                     =
                                                     let uu___12 =
                                                       match t_res_tm.FStarC_SMTEncoding_Term.tm
                                                       with
                                                       | FStarC_SMTEncoding_Term.App
                                                           (op, args) ->
                                                           let uu___13 =
                                                             FStarC_List.splitAt
                                                               (n_univs +
                                                                  n_tps) args in
                                                           (match uu___13
                                                            with
                                                            | (targs, iargs)
                                                                ->
                                                                let uu___14 =
                                                                  let uu___15
                                                                    =
                                                                    FStarC_List.map
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStarC_SMTEncoding_Env.fresh_fvar
                                                                    env2.FStarC_SMTEncoding_Env.current_module_name
                                                                    "i"
                                                                    FStarC_SMTEncoding_Term.Term_sort)
                                                                    iargs in
                                                                  FStarC_List.split
                                                                    uu___15 in
                                                                (match uu___14
                                                                 with
                                                                 | (fresh_ivars,
                                                                    fresh_iargs)
                                                                    ->
                                                                    let additional_guards
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_List.map2
                                                                    (fun a
                                                                    fresh_a
                                                                    ->
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    (a,
                                                                    fresh_a))
                                                                    iargs
                                                                    fresh_iargs in
                                                                    FStarC_SMTEncoding_Util.mk_and_l
                                                                    uu___15 in
                                                                    let uu___15
                                                                    =
                                                                    FStarC_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    fuel_tm)
                                                                    dapp
                                                                    {
                                                                    FStarC_SMTEncoding_Term.tm
                                                                    =
                                                                    (FStarC_SMTEncoding_Term.App
                                                                    (op,
                                                                    (FStarC_List.op_At
                                                                    targs
                                                                    fresh_iargs)));
                                                                    FStarC_SMTEncoding_Term.freevars
                                                                    =
                                                                    (t_res_tm.FStarC_SMTEncoding_Term.freevars);
                                                                    FStarC_SMTEncoding_Term.rng
                                                                    =
                                                                    (t_res_tm.FStarC_SMTEncoding_Term.rng)
                                                                    } in
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_List.map
                                                                    (fun s ->
                                                                    FStarC_SMTEncoding_Term.mk_fv
                                                                    (s,
                                                                    FStarC_SMTEncoding_Term.Term_sort))
                                                                    fresh_ivars in
                                                                    FStarC_List.op_At
                                                                    vars
                                                                    uu___17 in
                                                                    let uu___17
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkAnd
                                                                    (guard,
                                                                    additional_guards) in
                                                                    (uu___15,
                                                                    uu___16,
                                                                    uu___17)))
                                                       | uu___13 ->
                                                           (ty_pred', vars,
                                                             guard) in
                                                     match uu___12 with
                                                     | (ty_pred'1, vars1,
                                                        guard1) ->
                                                         let uu___13 =
                                                           let uu___14 =
                                                             let uu___15 =
                                                               FStarC_Ident.range_of_lid
                                                                 d in
                                                             let uu___16 =
                                                               let uu___17 =
                                                                 let uu___18
                                                                   =
                                                                   FStarC_SMTEncoding_Term.mk_fv
                                                                    (fuel_var,
                                                                    FStarC_SMTEncoding_Term.Fuel_sort) in
                                                                 FStarC_SMTEncoding_Env.add_fuel
                                                                   uu___18
                                                                   (FStarC_List.op_At
                                                                    univ_fvs
                                                                    vars1) in
                                                               let uu___18 =
                                                                 FStarC_SMTEncoding_Util.mkImp
                                                                   (guard1,
                                                                    ty_pred'1) in
                                                               ([[ty_pred'1]],
                                                                 uu___17,
                                                                 uu___18) in
                                                             FStarC_SMTEncoding_Term.mkForall
                                                               uu___15
                                                               uu___16 in
                                                           (uu___14,
                                                             (FStar_Pervasives_Native.Some
                                                                "data constructor typing intro"),
                                                             (Prims.strcat
                                                                "data_typing_intro_"
                                                                ddtok)) in
                                                         FStarC_SMTEncoding_Util.mkAssume
                                                           uu___13 in
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
                                                                    FStarC_Class_Show.show
                                                                    FStarC_Ident.showable_lident
                                                                    d in
                                                                    FStarC_Format.fmt1
                                                                    "data constructor proxy: %s"
                                                                    uu___22 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___21 in
                                                                    (ddtok,
                                                                    univ_sorts,
                                                                    FStarC_SMTEncoding_Term.Term_sort,
                                                                    uu___20) in
                                                                   FStarC_SMTEncoding_Term.DeclFun
                                                                    uu___19 in
                                                                 [uu___18] in
                                                               FStarC_List.op_At
                                                                 uu___17
                                                                 proxy_fresh in
                                                             FStarC_SMTEncoding_Term.mk_decls_trivial
                                                               uu___16 in
                                                           let uu___16 =
                                                             let uu___17 =
                                                               let uu___18 =
                                                                 let uu___19
                                                                   =
                                                                   let uu___20
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)) in
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
                                                                    FStarC_Ident.range_of_lid
                                                                    d in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStarC_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    (FStarC_List.op_At
                                                                    univ_fvs
                                                                    vars),
                                                                    uu___27) in
                                                                    FStarC_SMTEncoding_Term.mkForall
                                                                    uu___25
                                                                    uu___26 in
                                                                    (uu___24,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStarC_SMTEncoding_Util.mkAssume
                                                                    uu___23 in
                                                                    [uu___22;
                                                                    data_cons_typing_intro_decl] in
                                                                   uu___20 ::
                                                                    uu___21 in
                                                                 FStarC_List.op_At
                                                                   uu___19
                                                                   elim in
                                                               FStarC_SMTEncoding_Term.mk_decls_trivial
                                                                 uu___18 in
                                                             FStarC_List.op_At
                                                               decls_pred
                                                               uu___17 in
                                                           FStarC_List.op_At
                                                             uu___15 uu___16 in
                                                         FStarC_List.op_At
                                                           decls3 uu___14 in
                                                       FStarC_List.op_At
                                                         decls2 uu___13 in
                                                     FStarC_List.op_At
                                                       binder_decls uu___12 in
                                                   let uu___12 =
                                                     let uu___13 =
                                                       FStarC_SMTEncoding_Term.mk_decls_trivial
                                                         datacons in
                                                     FStarC_List.op_At
                                                       uu___13 g in
                                                   (uu___12, env2))))))))))
let rec encode_sigelt (env : FStarC_SMTEncoding_Env.env_t)
  (se : FStarC_Syntax_Syntax.sigelt) :
  (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.env_t)=
  let nm = FStarC_Syntax_Print.sigelt_to_string_short se in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Syntax_Print.sigelt_to_string_short se in
      FStarC_Format.fmt1 "While encoding top-level declaration `%s`" uu___2 in
    FStarC_Errors.with_ctx uu___1 (fun uu___2 -> encode_sigelt' env se) in
  match uu___ with
  | (g, env1) ->
      let g1 =
        match g with
        | [] ->
            ((let uu___2 = FStarC_Effect.op_Bang dbg_SMTEncoding in
              if uu___2
              then FStarC_Format.print1 "Skipped encoding of %s\n" nm
              else ());
             (let uu___2 =
                let uu___3 =
                  let uu___4 = FStarC_Format.fmt1 "<Skipped %s/>" nm in
                  FStarC_SMTEncoding_Term.Caption uu___4 in
                [uu___3; FStarC_SMTEncoding_Term.EmptyLine] in
              FStarC_SMTEncoding_Term.mk_decls_trivial uu___2))
        | uu___1 ->
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 = FStarC_Format.fmt1 "<Start encoding %s>" nm in
                  FStarC_SMTEncoding_Term.Caption uu___5 in
                [uu___4] in
              FStarC_SMTEncoding_Term.mk_decls_trivial uu___3 in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 = FStarC_Format.fmt1 "</end encoding %s>" nm in
                    FStarC_SMTEncoding_Term.Caption uu___7 in
                  [uu___6; FStarC_SMTEncoding_Term.EmptyLine] in
                FStarC_SMTEncoding_Term.mk_decls_trivial uu___5 in
              FStarC_List.op_At g uu___4 in
            FStarC_List.op_At uu___2 uu___3 in
      (g1, env1)
and encode_sigelt' (env : FStarC_SMTEncoding_Env.env_t)
  (se : FStarC_Syntax_Syntax.sigelt) :
  (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.env_t)=
  (let uu___1 = FStarC_Effect.op_Bang dbg_SMTEncoding in
   if uu___1
   then
     let uu___2 =
       FStarC_Class_Show.show FStarC_Syntax_Print.showable_sigelt se in
     FStarC_Format.print1 "@@@Encoding sigelt %s\n" uu___2
   else ());
  (let is_opaque_to_smt t =
     let uu___1 =
       let uu___2 = FStarC_Syntax_Subst.compress t in
       uu___2.FStarC_Syntax_Syntax.n in
     match uu___1 with
     | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_string
         (s, uu___2)) -> s = "opaque_to_smt"
     | uu___2 -> false in
   let is_uninterpreted_by_smt t =
     let uu___1 =
       let uu___2 = FStarC_Syntax_Subst.compress t in
       uu___2.FStarC_Syntax_Syntax.n in
     match uu___1 with
     | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_string
         (s, uu___2)) -> s = "uninterpreted_by_smt"
     | uu___2 -> false in
   match se.FStarC_Syntax_Syntax.sigel with
   | FStarC_Syntax_Syntax.Sig_splice uu___1 ->
       failwith "impossible -- splice should have been removed by Tc.fs"
   | FStarC_Syntax_Syntax.Sig_fail uu___1 ->
       failwith "impossible -- Sig_fail should have been removed by Tc.fs"
   | FStarC_Syntax_Syntax.Sig_pragma uu___1 -> ([], env)
   | FStarC_Syntax_Syntax.Sig_effect_abbrev uu___1 -> ([], env)
   | FStarC_Syntax_Syntax.Sig_sub_effect uu___1 -> ([], env)
   | FStarC_Syntax_Syntax.Sig_polymonadic_bind uu___1 -> ([], env)
   | FStarC_Syntax_Syntax.Sig_polymonadic_subcomp uu___1 -> ([], env)
   | FStarC_Syntax_Syntax.Sig_new_effect ed ->
       let uu___1 =
         let uu___2 =
           FStarC_SMTEncoding_Util.is_smt_reifiable_effect
             env.FStarC_SMTEncoding_Env.tcenv ed.FStarC_Syntax_Syntax.mname in
         Prims.op_Negation uu___2 in
       if uu___1
       then ([], env)
       else
         (let uu___3 =
            FStarC_Syntax_Subst.univ_var_opening
              ed.FStarC_Syntax_Syntax.univs in
          match uu___3 with
          | (ed_univs_subst, ed_univs) ->
              let close_effect_params tm =
                let uu___4 =
                  match ed.FStarC_Syntax_Syntax.binders with
                  | [] -> tm
                  | uu___5 ->
                      let uu___6 =
                        let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              FStarC_Syntax_Util.mk_residual_comp
                                FStarC_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStarC_Syntax_Syntax.TOTAL] in
                            FStar_Pervasives_Native.Some uu___9 in
                          {
                            FStarC_Syntax_Syntax.bs =
                              (ed.FStarC_Syntax_Syntax.binders);
                            FStarC_Syntax_Syntax.body = tm;
                            FStarC_Syntax_Syntax.rc_opt = uu___8
                          } in
                        FStarC_Syntax_Syntax.Tm_abs uu___7 in
                      FStarC_Syntax_Syntax.mk uu___6
                        tm.FStarC_Syntax_Syntax.pos in
                FStarC_Syntax_Subst.subst ed_univs_subst uu___4 in
              let open_action_univs a =
                let uu___4 =
                  FStarC_Syntax_Subst.univ_var_opening
                    a.FStarC_Syntax_Syntax.action_univs in
                match uu___4 with
                | (action_univs_subst, action_univs) ->
                    let uu___5 =
                      let uu___6 =
                        FStarC_Syntax_Subst.subst action_univs_subst
                          a.FStarC_Syntax_Syntax.action_defn in
                      FStarC_Syntax_Subst.subst ed_univs_subst uu___6 in
                    let uu___6 =
                      let uu___7 =
                        FStarC_Syntax_Subst.subst action_univs_subst
                          a.FStarC_Syntax_Syntax.action_typ in
                      FStarC_Syntax_Subst.subst ed_univs_subst uu___7 in
                    (uu___5, uu___6, action_univs) in
              let encode_action env1 a =
                let uu___4 =
                  FStarC_Syntax_Subst.univ_var_opening
                    a.FStarC_Syntax_Syntax.action_univs in
                match uu___4 with
                | (action_univs_subst, action_univs) ->
                    let uu___5 = open_action_univs a in
                    (match uu___5 with
                     | (action_defn, action_typ, action_univs1) ->
                         let action_defn1 =
                           let uu___6 = close_effect_params action_defn in
                           norm_before_encoding env1 uu___6 in
                         let uu___6 =
                           FStarC_Syntax_Util.arrow_formals_comp action_typ in
                         (match uu___6 with
                          | (formals, uu___7) ->
                              let arity = FStarC_List.length formals in
                              let univ_arity =
                                (FStarC_List.length action_univs1) +
                                  (FStarC_List.length ed_univs) in
                              let uu___8 =
                                FStarC_SMTEncoding_Env.new_term_constant_and_tok_from_lid
                                  env1 a.FStarC_Syntax_Syntax.action_name
                                  arity univ_arity in
                              (match uu___8 with
                               | (aname, atok, env2) ->
                                   let uu___9 =
                                     FStarC_SMTEncoding_EncodeTerm.encode_term
                                       action_defn1 env2 in
                                   (match uu___9 with
                                    | (tm, decls) ->
                                        let univ_sorts =
                                          FStarC_List.map
                                            (fun uu___10 ->
                                               FStarC_SMTEncoding_Term.univ_sort)
                                            (FStarC_List.op_At ed_univs
                                               action_univs1) in
                                        let a_decls =
                                          let uu___10 =
                                            let uu___11 =
                                              let uu___12 =
                                                let uu___13 =
                                                  FStarC_List.map
                                                    (fun uu___14 ->
                                                       FStarC_SMTEncoding_Term.Term_sort)
                                                    formals in
                                                FStarC_List.op_At univ_sorts
                                                  uu___13 in
                                              (aname, uu___12,
                                                FStarC_SMTEncoding_Term.Term_sort,
                                                (FStar_Pervasives_Native.Some
                                                   "Action")) in
                                            FStarC_SMTEncoding_Term.DeclFun
                                              uu___11 in
                                          [uu___10;
                                          FStarC_SMTEncoding_Term.DeclFun
                                            (atok, univ_sorts,
                                              FStarC_SMTEncoding_Term.Term_sort,
                                              (FStar_Pervasives_Native.Some
                                                 "Action token"))] in
                                        let uu___10 =
                                          let aux u uu___11 =
                                            match uu___11 with
                                            | (env3, acc_sorts, acc) ->
                                                let uu___12 =
                                                  FStarC_SMTEncoding_EncodeTerm.encode_univ_name
                                                    u in
                                                (match uu___12 with
                                                 | (fv, tm1) ->
                                                     (env3, (fv ::
                                                       acc_sorts), (tm1 ::
                                                       acc))) in
                                          FStarC_List.fold_right aux
                                            (FStarC_List.op_At ed_univs
                                               action_univs1) (env2, [], []) in
                                        (match uu___10 with
                                         | (uu___11, us_sorts, us) ->
                                             let uu___12 =
                                               let aux uu___13 uu___14 =
                                                 match (uu___13, uu___14)
                                                 with
                                                 | ({
                                                      FStarC_Syntax_Syntax.binder_bv
                                                        = bv;
                                                      FStarC_Syntax_Syntax.binder_qual
                                                        = uu___15;
                                                      FStarC_Syntax_Syntax.binder_positivity
                                                        = uu___16;
                                                      FStarC_Syntax_Syntax.binder_attrs
                                                        = uu___17;_},
                                                    (env3, acc_sorts, acc))
                                                     ->
                                                     let uu___18 =
                                                       FStarC_SMTEncoding_Env.gen_term_var
                                                         env3 bv in
                                                     (match uu___18 with
                                                      | (xxsym, xx, env4) ->
                                                          let uu___19 =
                                                            let uu___20 =
                                                              FStarC_SMTEncoding_Term.mk_fv
                                                                (xxsym,
                                                                  FStarC_SMTEncoding_Term.Term_sort) in
                                                            uu___20 ::
                                                              acc_sorts in
                                                          (env4, uu___19, (xx
                                                            :: acc))) in
                                               FStarC_List.fold_right aux
                                                 formals (env2, [], []) in
                                             (match uu___12 with
                                              | (uu___13, xs_sorts, xs) ->
                                                  let app =
                                                    FStarC_SMTEncoding_Util.mkApp
                                                      (aname,
                                                        (FStarC_List.op_At us
                                                           xs)) in
                                                  let a_eq =
                                                    let uu___14 =
                                                      let uu___15 =
                                                        let uu___16 =
                                                          FStarC_Ident.range_of_lid
                                                            a.FStarC_Syntax_Syntax.action_name in
                                                        let uu___17 =
                                                          let uu___18 =
                                                            let uu___19 =
                                                              let uu___20 =
                                                                FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                                                  tm xs_sorts in
                                                              (app, uu___20) in
                                                            FStarC_SMTEncoding_Util.mkEq
                                                              uu___19 in
                                                          ([[app]],
                                                            (FStarC_List.op_At
                                                               us_sorts
                                                               xs_sorts),
                                                            uu___18) in
                                                        FStarC_SMTEncoding_Term.mkForall
                                                          uu___16 uu___17 in
                                                      (uu___15,
                                                        (FStar_Pervasives_Native.Some
                                                           "Action equality"),
                                                        (Prims.strcat aname
                                                           "_equality")) in
                                                    FStarC_SMTEncoding_Util.mkAssume
                                                      uu___14 in
                                                  let tok_correspondence =
                                                    let tok_term =
                                                      FStarC_SMTEncoding_Util.mkApp
                                                        (atok, us) in
                                                    let tok_app =
                                                      FStarC_SMTEncoding_EncodeTerm.mk_Apply
                                                        tok_term xs_sorts in
                                                    let uu___14 =
                                                      let uu___15 =
                                                        let uu___16 =
                                                          FStarC_Ident.range_of_lid
                                                            a.FStarC_Syntax_Syntax.action_name in
                                                        let uu___17 =
                                                          let uu___18 =
                                                            FStarC_SMTEncoding_Util.mkEq
                                                              (tok_app, app) in
                                                          ([[tok_app]],
                                                            (FStarC_List.op_At
                                                               us_sorts
                                                               xs_sorts),
                                                            uu___18) in
                                                        FStarC_SMTEncoding_Term.mkForall
                                                          uu___16 uu___17 in
                                                      (uu___15,
                                                        (FStar_Pervasives_Native.Some
                                                           "Action token correspondence"),
                                                        (Prims.strcat aname
                                                           "_token_correspondence")) in
                                                    FStarC_SMTEncoding_Util.mkAssume
                                                      uu___14 in
                                                  let uu___14 =
                                                    let uu___15 =
                                                      FStarC_SMTEncoding_Term.mk_decls_trivial
                                                        (FStarC_List.op_At
                                                           a_decls
                                                           [a_eq;
                                                           tok_correspondence]) in
                                                    FStarC_List.op_At decls
                                                      uu___15 in
                                                  (env2, uu___14))))))) in
              let uu___4 =
                FStarC_Util.fold_map encode_action env
                  ed.FStarC_Syntax_Syntax.actions in
              (match uu___4 with
               | (env1, decls2) -> ((FStarC_List.flatten decls2), env1)))
   | FStarC_Syntax_Syntax.Sig_declare_typ
       { FStarC_Syntax_Syntax.lid2 = lid; FStarC_Syntax_Syntax.us2 = uu___1;
         FStarC_Syntax_Syntax.t2 = uu___2;_}
       when FStarC_Ident.lid_equals lid FStarC_Parser_Const.precedes_lid ->
       let uu___3 =
         FStarC_SMTEncoding_Env.new_term_constant_and_tok_from_lid env lid
           (Prims.of_int (4)) (Prims.of_int (2)) in
       (match uu___3 with | (tname, ttok, env1) -> ([], env1))
   | FStarC_Syntax_Syntax.Sig_declare_typ
       { FStarC_Syntax_Syntax.lid2 = lid; FStarC_Syntax_Syntax.us2 = us;
         FStarC_Syntax_Syntax.t2 = t;_}
       ->
       let uu___1 = FStarC_Syntax_Subst.open_univ_vars us t in
       (match uu___1 with
        | (us1, t1) ->
            let env1 =
              let uu___2 =
                FStarC_TypeChecker_Env.push_univ_vars
                  env.FStarC_SMTEncoding_Env.tcenv us1 in
              {
                FStarC_SMTEncoding_Env.bvar_bindings =
                  (env.FStarC_SMTEncoding_Env.bvar_bindings);
                FStarC_SMTEncoding_Env.fvar_bindings =
                  (env.FStarC_SMTEncoding_Env.fvar_bindings);
                FStarC_SMTEncoding_Env.depth =
                  (env.FStarC_SMTEncoding_Env.depth);
                FStarC_SMTEncoding_Env.tcenv = uu___2;
                FStarC_SMTEncoding_Env.warn =
                  (env.FStarC_SMTEncoding_Env.warn);
                FStarC_SMTEncoding_Env.nolabels =
                  (env.FStarC_SMTEncoding_Env.nolabels);
                FStarC_SMTEncoding_Env.use_zfuel_name =
                  (env.FStarC_SMTEncoding_Env.use_zfuel_name);
                FStarC_SMTEncoding_Env.encode_non_total_function_typ =
                  (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
                FStarC_SMTEncoding_Env.current_module_name =
                  (env.FStarC_SMTEncoding_Env.current_module_name);
                FStarC_SMTEncoding_Env.encoding_quantifier =
                  (env.FStarC_SMTEncoding_Env.encoding_quantifier);
                FStarC_SMTEncoding_Env.global_cache =
                  (env.FStarC_SMTEncoding_Env.global_cache)
              } in
            let quals = se.FStarC_Syntax_Syntax.sigquals in
            let will_encode_definition =
              let uu___2 =
                FStarC_Util.for_some
                  (fun uu___3 ->
                     match uu___3 with
                     | FStarC_Syntax_Syntax.Assumption -> true
                     | FStarC_Syntax_Syntax.Projector uu___4 -> true
                     | FStarC_Syntax_Syntax.Discriminator uu___4 -> true
                     | FStarC_Syntax_Syntax.Irreducible -> true
                     | uu___4 -> false) quals in
              Prims.op_Negation uu___2 in
            if will_encode_definition
            then ([], env1)
            else
              (let fv =
                 FStarC_Syntax_Syntax.lid_as_fv lid
                   FStar_Pervasives_Native.None in
               let uu___3 =
                 let uu___4 =
                   FStarC_Util.for_some is_uninterpreted_by_smt
                     se.FStarC_Syntax_Syntax.sigattrs in
                 encode_top_level_val uu___4 env1 us1 fv t1 quals in
               match uu___3 with
               | (decls, env2) ->
                   let tname = FStarC_Ident.string_of_lid lid in
                   let tsym =
                     let uu___4 =
                       FStarC_SMTEncoding_Env.try_lookup_free_var env2 lid in
                     FStarC_Option.must uu___4 in
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         primitive_type_axioms
                           env2.FStarC_SMTEncoding_Env.tcenv lid tname tsym in
                       FStarC_SMTEncoding_Term.mk_decls_trivial uu___6 in
                     FStarC_List.op_At decls uu___5 in
                   (uu___4, env2)))
   | FStarC_Syntax_Syntax.Sig_assume
       { FStarC_Syntax_Syntax.lid3 = l; FStarC_Syntax_Syntax.us3 = us;
         FStarC_Syntax_Syntax.phi1 = f;_}
       ->
       let uu___1 = FStarC_Syntax_Subst.open_univ_vars us f in
       (match uu___1 with
        | (uvs, f1) ->
            let env1 =
              let uu___2 =
                FStarC_TypeChecker_Env.push_univ_vars
                  env.FStarC_SMTEncoding_Env.tcenv uvs in
              {
                FStarC_SMTEncoding_Env.bvar_bindings =
                  (env.FStarC_SMTEncoding_Env.bvar_bindings);
                FStarC_SMTEncoding_Env.fvar_bindings =
                  (env.FStarC_SMTEncoding_Env.fvar_bindings);
                FStarC_SMTEncoding_Env.depth =
                  (env.FStarC_SMTEncoding_Env.depth);
                FStarC_SMTEncoding_Env.tcenv = uu___2;
                FStarC_SMTEncoding_Env.warn =
                  (env.FStarC_SMTEncoding_Env.warn);
                FStarC_SMTEncoding_Env.nolabels =
                  (env.FStarC_SMTEncoding_Env.nolabels);
                FStarC_SMTEncoding_Env.use_zfuel_name =
                  (env.FStarC_SMTEncoding_Env.use_zfuel_name);
                FStarC_SMTEncoding_Env.encode_non_total_function_typ =
                  (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
                FStarC_SMTEncoding_Env.current_module_name =
                  (env.FStarC_SMTEncoding_Env.current_module_name);
                FStarC_SMTEncoding_Env.encoding_quantifier =
                  (env.FStarC_SMTEncoding_Env.encoding_quantifier);
                FStarC_SMTEncoding_Env.global_cache =
                  (env.FStarC_SMTEncoding_Env.global_cache)
              } in
            let f2 = norm_before_encoding env1 f1 in
            let uu___2 = FStarC_SMTEncoding_EncodeTerm.encode_formula f2 env1 in
            (match uu___2 with
             | (f3, decls) ->
                 let f4 =
                   let uu___3 =
                     let uu___4 =
                       FStarC_List.map
                         FStarC_SMTEncoding_EncodeTerm.encode_univ_name uvs in
                     FStarC_List.unzip uu___4 in
                   match uu___3 with
                   | (univ_fvs, univ_tms) ->
                       let uu___4 = FStarC_Ident.range_of_lid l in
                       FStarC_SMTEncoding_Term.mkForall uu___4
                         ([], univ_fvs, f3) in
                 let g =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           let uu___7 =
                             let uu___8 =
                               FStarC_Class_Show.show
                                 FStarC_Ident.showable_lident l in
                             FStarC_Format.fmt1 "Assumption: %s" uu___8 in
                           FStar_Pervasives_Native.Some uu___7 in
                         let uu___7 =
                           let uu___8 =
                             let uu___9 = FStarC_Ident.string_of_lid l in
                             Prims.strcat "assumption_" uu___9 in
                           FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.mk_unique
                             uu___8 in
                         (f4, uu___6, uu___7) in
                       FStarC_SMTEncoding_Util.mkAssume uu___5 in
                     [uu___4] in
                   FStarC_SMTEncoding_Term.mk_decls_trivial uu___3 in
                 ((FStarC_List.op_At decls g), env1)))
   | FStarC_Syntax_Syntax.Sig_let
       { FStarC_Syntax_Syntax.lbs1 = lbs;
         FStarC_Syntax_Syntax.lids1 = uu___1;_}
       when
       (FStarC_List.contains FStarC_Syntax_Syntax.Irreducible
          se.FStarC_Syntax_Syntax.sigquals)
         ||
         (FStarC_Util.for_some is_opaque_to_smt
            se.FStarC_Syntax_Syntax.sigattrs)
       ->
       let attrs = se.FStarC_Syntax_Syntax.sigattrs in
       let uu___2 =
         FStarC_Util.fold_map
           (fun env1 lb ->
              let lid =
                (FStar_Pervasives.__proj__Inr__item__v
                   lb.FStarC_Syntax_Syntax.lbname).FStarC_Syntax_Syntax.fv_name in
              let uu___3 =
                let uu___4 =
                  FStarC_TypeChecker_Env.try_lookup_val_decl
                    env1.FStarC_SMTEncoding_Env.tcenv lid in
                FStar_Pervasives_Native.uu___is_None uu___4 in
              if uu___3
              then
                let val_decl =
                  {
                    FStarC_Syntax_Syntax.sigel =
                      (FStarC_Syntax_Syntax.Sig_declare_typ
                         {
                           FStarC_Syntax_Syntax.lid2 = lid;
                           FStarC_Syntax_Syntax.us2 =
                             (lb.FStarC_Syntax_Syntax.lbunivs);
                           FStarC_Syntax_Syntax.t2 =
                             (lb.FStarC_Syntax_Syntax.lbtyp)
                         });
                    FStarC_Syntax_Syntax.sigrng =
                      (se.FStarC_Syntax_Syntax.sigrng);
                    FStarC_Syntax_Syntax.sigquals =
                      (FStarC_Syntax_Syntax.Irreducible ::
                      (se.FStarC_Syntax_Syntax.sigquals));
                    FStarC_Syntax_Syntax.sigmeta =
                      (se.FStarC_Syntax_Syntax.sigmeta);
                    FStarC_Syntax_Syntax.sigattrs =
                      (se.FStarC_Syntax_Syntax.sigattrs);
                    FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                      (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                    FStarC_Syntax_Syntax.sigopts =
                      (se.FStarC_Syntax_Syntax.sigopts)
                  } in
                let uu___4 = encode_sigelt' env1 val_decl in
                match uu___4 with | (decls, env2) -> (env2, decls)
              else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
       (match uu___2 with
        | (env1, decls) -> ((FStarC_List.flatten decls), env1))
   | FStarC_Syntax_Syntax.Sig_let
       {
         FStarC_Syntax_Syntax.lbs1 =
           (uu___1,
            { FStarC_Syntax_Syntax.lbname = FStar_Pervasives.Inr b2t;
              FStarC_Syntax_Syntax.lbunivs = uu___2;
              FStarC_Syntax_Syntax.lbtyp = uu___3;
              FStarC_Syntax_Syntax.lbeff = uu___4;
              FStarC_Syntax_Syntax.lbdef = uu___5;
              FStarC_Syntax_Syntax.lbattrs = uu___6;
              FStarC_Syntax_Syntax.lbpos = uu___7;_}::[]);
         FStarC_Syntax_Syntax.lids1 = uu___8;_}
       when FStarC_Syntax_Syntax.fv_eq_lid b2t FStarC_Parser_Const.b2t_lid ->
       let uu___9 =
         FStarC_SMTEncoding_Env.new_term_constant_and_tok_from_lid env
           b2t.FStarC_Syntax_Syntax.fv_name Prims.int_one Prims.int_zero in
       (match uu___9 with
        | (tname, ttok, env1) ->
            let xx =
              FStarC_SMTEncoding_Term.mk_fv
                ("x", FStarC_SMTEncoding_Term.Term_sort) in
            let x = FStarC_SMTEncoding_Util.mkFreeV xx in
            let b2t_x = FStarC_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
            let valid_b2t_x =
              FStarC_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
            let bool_ty =
              FStarC_SMTEncoding_Env.lookup_free_var env1
                FStarC_Parser_Const.bool_lid in
            let decls =
              let uu___10 =
                let uu___11 =
                  let uu___12 =
                    let uu___13 =
                      let uu___14 = FStarC_Syntax_Syntax.range_of_fv b2t in
                      let uu___15 =
                        let uu___16 =
                          let uu___17 =
                            let uu___18 =
                              FStarC_SMTEncoding_Util.mkApp
                                ((FStar_Pervasives_Native.snd
                                    FStarC_SMTEncoding_Term.boxBoolFun), 
                                  [x]) in
                            (valid_b2t_x, uu___18) in
                          FStarC_SMTEncoding_Util.mkEq uu___17 in
                        ([[b2t_x]], [xx], uu___16) in
                      FStarC_SMTEncoding_Term.mkForall uu___14 uu___15 in
                    (uu___13, (FStar_Pervasives_Native.Some "b2t def"),
                      "b2t_def") in
                  FStarC_SMTEncoding_Util.mkAssume uu___12 in
                let uu___12 =
                  let uu___13 =
                    let uu___14 =
                      let uu___15 =
                        let uu___16 = FStarC_Syntax_Syntax.range_of_fv b2t in
                        let uu___17 =
                          let uu___18 =
                            let uu___19 =
                              let uu___20 =
                                FStarC_SMTEncoding_Term.mk_HasType x bool_ty in
                              let uu___21 =
                                let uu___22 =
                                  FStarC_SMTEncoding_Term.mk_Term_type
                                    FStarC_SMTEncoding_Term.mk_U_zero in
                                FStarC_SMTEncoding_Term.mk_HasType b2t_x
                                  uu___22 in
                              (uu___20, uu___21) in
                            FStarC_SMTEncoding_Util.mkImp uu___19 in
                          ([[b2t_x]], [xx], uu___18) in
                        FStarC_SMTEncoding_Term.mkForall uu___16 uu___17 in
                      (uu___15, (FStar_Pervasives_Native.Some "b2t typing"),
                        "b2t_typing") in
                    FStarC_SMTEncoding_Util.mkAssume uu___14 in
                  [uu___13] in
                uu___11 :: uu___12 in
              (FStarC_SMTEncoding_Term.DeclFun
                 (tname, [FStarC_SMTEncoding_Term.Term_sort],
                   FStarC_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None))
                :: uu___10 in
            let uu___10 = FStarC_SMTEncoding_Term.mk_decls_trivial decls in
            (uu___10, env1))
   | FStarC_Syntax_Syntax.Sig_let uu___1 when
       FStarC_Util.for_some
         (fun uu___2 ->
            match uu___2 with
            | FStarC_Syntax_Syntax.Discriminator uu___3 -> true
            | uu___3 -> false) se.FStarC_Syntax_Syntax.sigquals
       ->
       ((let uu___3 = FStarC_Effect.op_Bang dbg_SMTEncoding in
         if uu___3
         then
           let uu___4 = FStarC_Syntax_Print.sigelt_to_string_short se in
           FStarC_Format.print1 "Not encoding discriminator '%s'\n" uu___4
         else ());
        ([], env))
   | FStarC_Syntax_Syntax.Sig_let
       { FStarC_Syntax_Syntax.lbs1 = uu___1;
         FStarC_Syntax_Syntax.lids1 = lids;_}
       when
       (FStarC_Util.for_some
          (fun l ->
             let uu___2 =
               let uu___3 =
                 let uu___4 = FStarC_Ident.ns_of_lid l in
                 FStarC_List.hd uu___4 in
               FStarC_Ident.string_of_id uu___3 in
             uu___2 = "Prims") lids)
         &&
         (FStarC_Util.for_some
            (fun uu___2 ->
               match uu___2 with
               | FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen ->
                   true
               | uu___3 -> false) se.FStarC_Syntax_Syntax.sigquals)
       ->
       ((let uu___3 = FStarC_Effect.op_Bang dbg_SMTEncoding in
         if uu___3
         then
           let uu___4 = FStarC_Syntax_Print.sigelt_to_string_short se in
           FStarC_Format.print1 "Not encoding unfold let from Prims '%s'\n"
             uu___4
         else ());
        ([], env))
   | FStarC_Syntax_Syntax.Sig_let
       { FStarC_Syntax_Syntax.lbs1 = (false, lb::[]);
         FStarC_Syntax_Syntax.lids1 = uu___1;_}
       when
       FStarC_Util.for_some
         (fun uu___2 ->
            match uu___2 with
            | FStarC_Syntax_Syntax.Projector uu___3 -> true
            | uu___3 -> false) se.FStarC_Syntax_Syntax.sigquals
       ->
       let fv =
         FStar_Pervasives.__proj__Inr__item__v lb.FStarC_Syntax_Syntax.lbname in
       let l = fv.FStarC_Syntax_Syntax.fv_name in
       let uu___2 = FStarC_SMTEncoding_Env.try_lookup_free_var env l in
       (match uu___2 with
        | FStar_Pervasives_Native.Some uu___3 -> ([], env)
        | FStar_Pervasives_Native.None ->
            let se1 =
              let uu___3 = FStarC_Ident.range_of_lid l in
              {
                FStarC_Syntax_Syntax.sigel =
                  (FStarC_Syntax_Syntax.Sig_declare_typ
                     {
                       FStarC_Syntax_Syntax.lid2 = l;
                       FStarC_Syntax_Syntax.us2 =
                         (lb.FStarC_Syntax_Syntax.lbunivs);
                       FStarC_Syntax_Syntax.t2 =
                         (lb.FStarC_Syntax_Syntax.lbtyp)
                     });
                FStarC_Syntax_Syntax.sigrng = uu___3;
                FStarC_Syntax_Syntax.sigquals =
                  (se.FStarC_Syntax_Syntax.sigquals);
                FStarC_Syntax_Syntax.sigmeta =
                  (se.FStarC_Syntax_Syntax.sigmeta);
                FStarC_Syntax_Syntax.sigattrs =
                  (se.FStarC_Syntax_Syntax.sigattrs);
                FStarC_Syntax_Syntax.sigopens_and_abbrevs =
                  (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
                FStarC_Syntax_Syntax.sigopts =
                  (se.FStarC_Syntax_Syntax.sigopts)
              } in
            encode_sigelt env se1)
   | FStarC_Syntax_Syntax.Sig_let
       { FStarC_Syntax_Syntax.lbs1 = (is_rec, bindings);
         FStarC_Syntax_Syntax.lids1 = uu___1;_}
       ->
       let uu___2 =
         FStarC_Syntax_Subst.open_let_rec bindings
           FStarC_Syntax_Util.exp_unit in
       (match uu___2 with
        | (bindings1, uu___3) ->
            let bindings2 =
              FStarC_List.map
                (fun lb ->
                   let def =
                     norm_before_encoding_us env
                       lb.FStarC_Syntax_Syntax.lbunivs
                       lb.FStarC_Syntax_Syntax.lbdef in
                   let typ =
                     norm_before_encoding_us env
                       lb.FStarC_Syntax_Syntax.lbunivs
                       lb.FStarC_Syntax_Syntax.lbtyp in
                   {
                     FStarC_Syntax_Syntax.lbname =
                       (lb.FStarC_Syntax_Syntax.lbname);
                     FStarC_Syntax_Syntax.lbunivs =
                       (lb.FStarC_Syntax_Syntax.lbunivs);
                     FStarC_Syntax_Syntax.lbtyp = typ;
                     FStarC_Syntax_Syntax.lbeff =
                       (lb.FStarC_Syntax_Syntax.lbeff);
                     FStarC_Syntax_Syntax.lbdef = def;
                     FStarC_Syntax_Syntax.lbattrs =
                       (lb.FStarC_Syntax_Syntax.lbattrs);
                     FStarC_Syntax_Syntax.lbpos =
                       (lb.FStarC_Syntax_Syntax.lbpos)
                   }) bindings1 in
            let uu___4 =
              FStarC_Syntax_Subst.close_let_rec bindings2
                FStarC_Syntax_Util.exp_unit in
            (match uu___4 with
             | (bindings3, uu___5) ->
                 encode_top_level_let env (is_rec, bindings3)
                   se.FStarC_Syntax_Syntax.sigquals))
   | FStarC_Syntax_Syntax.Sig_bundle
       { FStarC_Syntax_Syntax.ses = ses; FStarC_Syntax_Syntax.lids = lids;_}
       when
       FStarC_Util.for_some
         (FStarC_Ident.lid_equals FStarC_Parser_Const.lex_t_lid) lids
       -> ([], env)
   | FStarC_Syntax_Syntax.Sig_bundle
       { FStarC_Syntax_Syntax.ses = ses;
         FStarC_Syntax_Syntax.lids = uu___1;_}
       ->
       let uu___2 =
         FStarC_List.fold_left
           (fun uu___3 se1 ->
              match uu___3 with
              | (g, env1) ->
                  let uu___4 =
                    match se1.FStarC_Syntax_Syntax.sigel with
                    | FStarC_Syntax_Syntax.Sig_inductive_typ uu___5 ->
                        encode_sig_inductive env1 se1
                    | FStarC_Syntax_Syntax.Sig_datacon uu___5 ->
                        encode_datacon env1 se1
                    | uu___5 -> encode_sigelt env1 se1 in
                  (match uu___4 with
                   | (g', env2) -> ((FStarC_List.op_At g g'), env2)))
           ([], env) ses in
       (match uu___2 with
        | (g, env1) ->
            let uu___3 =
              FStarC_List.fold_left
                (fun uu___4 elt ->
                   match uu___4 with
                   | (g', inversions) ->
                       let uu___5 =
                         FStarC_List.partition
                           (fun uu___6 ->
                              match uu___6 with
                              | FStarC_SMTEncoding_Term.Assume
                                  {
                                    FStarC_SMTEncoding_Term.assumption_term =
                                      uu___7;
                                    FStarC_SMTEncoding_Term.assumption_caption
                                      = FStar_Pervasives_Native.Some
                                      "inversion axiom";
                                    FStarC_SMTEncoding_Term.assumption_name =
                                      uu___8;
                                    FStarC_SMTEncoding_Term.assumption_fact_ids
                                      = uu___9;
                                    FStarC_SMTEncoding_Term.assumption_free_names
                                      = uu___10;_}
                                  -> false
                              | uu___7 -> true)
                           elt.FStarC_SMTEncoding_Term.decls in
                       (match uu___5 with
                        | (elt_g', elt_inversions) ->
                            ((FStarC_List.op_At g'
                                [{
                                   FStarC_SMTEncoding_Term.sym_name =
                                     (elt.FStarC_SMTEncoding_Term.sym_name);
                                   FStarC_SMTEncoding_Term.key =
                                     (elt.FStarC_SMTEncoding_Term.key);
                                   FStarC_SMTEncoding_Term.decls = elt_g';
                                   FStarC_SMTEncoding_Term.a_names =
                                     (elt.FStarC_SMTEncoding_Term.a_names)
                                 }]),
                              (FStarC_List.op_At inversions elt_inversions))))
                ([], []) g in
            (match uu___3 with
             | (g', inversions) ->
                 let uu___4 =
                   FStarC_List.fold_left
                     (fun uu___5 elt ->
                        match uu___5 with
                        | (decls, elts, rest) ->
                            let uu___6 =
                              (FStar_Pervasives_Native.uu___is_Some
                                 elt.FStarC_SMTEncoding_Term.key)
                                &&
                                (FStarC_List.existsb
                                   (fun uu___7 ->
                                      match uu___7 with
                                      | FStarC_SMTEncoding_Term.DeclFun
                                          uu___8 -> true
                                      | uu___8 -> false)
                                   elt.FStarC_SMTEncoding_Term.decls) in
                            if uu___6
                            then
                              (decls, (FStarC_List.op_At elts [elt]), rest)
                            else
                              (let uu___8 =
                                 FStarC_List.partition
                                   (fun uu___9 ->
                                      match uu___9 with
                                      | FStarC_SMTEncoding_Term.DeclFun
                                          uu___10 -> true
                                      | uu___10 -> false)
                                   elt.FStarC_SMTEncoding_Term.decls in
                               match uu___8 with
                               | (elt_decls, elt_rest) ->
                                   ((FStarC_List.op_At decls elt_decls),
                                     elts,
                                     (FStarC_List.op_At rest
                                        [{
                                           FStarC_SMTEncoding_Term.sym_name =
                                             (elt.FStarC_SMTEncoding_Term.sym_name);
                                           FStarC_SMTEncoding_Term.key =
                                             (elt.FStarC_SMTEncoding_Term.key);
                                           FStarC_SMTEncoding_Term.decls =
                                             elt_rest;
                                           FStarC_SMTEncoding_Term.a_names =
                                             (elt.FStarC_SMTEncoding_Term.a_names)
                                         }])))) ([], [], []) g' in
                 (match uu___4 with
                  | (decls, elts, rest) ->
                      let uu___5 =
                        let uu___6 =
                          FStarC_SMTEncoding_Term.mk_decls_trivial decls in
                        let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              FStarC_SMTEncoding_Term.mk_decls_trivial
                                inversions in
                            FStarC_List.op_At rest uu___9 in
                          FStarC_List.op_At elts uu___8 in
                        FStarC_List.op_At uu___6 uu___7 in
                      (uu___5, env1)))))
let encode_env_bindings (env : FStarC_SMTEncoding_Env.env_t)
  (bindings : FStarC_Syntax_Syntax.binding Prims.list) :
  (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.env_t)=
  let encode_binding b uu___ =
    match uu___ with
    | (i, decls, env1) ->
        (match b with
         | FStarC_Syntax_Syntax.Binding_univ u ->
             let uu___1 = FStarC_SMTEncoding_EncodeTerm.encode_univ_name u in
             (match uu___1 with
              | (u_fv, u_tm) ->
                  let decls' =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStarC_SMTEncoding_Term.fv_name u_fv in
                          (uu___5, [], FStarC_SMTEncoding_Term.univ_sort,
                            (FStar_Pervasives_Native.Some
                               "universe local constant")) in
                        FStarC_SMTEncoding_Term.DeclFun uu___4 in
                      [uu___3] in
                    FStarC_SMTEncoding_Term.mk_decls_trivial uu___2 in
                  ((i + Prims.int_one), (FStarC_List.op_At decls decls'),
                    env1))
         | FStarC_Syntax_Syntax.Binding_var x ->
             let t1 = norm_before_encoding env1 x.FStarC_Syntax_Syntax.sort in
             ((let uu___2 = FStarC_Effect.op_Bang dbg_SMTEncoding in
               if uu___2
               then
                 let uu___3 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x in
                 let uu___4 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     x.FStarC_Syntax_Syntax.sort in
                 let uu___5 =
                   FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                     t1 in
                 FStarC_Format.print3 "Normalized %s : %s to %s\n" uu___3
                   uu___4 uu___5
               else ());
              (let uu___2 = FStarC_SMTEncoding_EncodeTerm.encode_term t1 env1 in
               match uu___2 with
               | (t, decls') ->
                   let t_hash = FStarC_SMTEncoding_Term.hash_of_term t in
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = FStarC_Util.digest_of_string t_hash in
                         let uu___7 =
                           let uu___8 =
                             FStarC_Class_Show.show
                               FStarC_Class_Show.showable_int i in
                           Prims.strcat "_" uu___8 in
                         Prims.strcat uu___6 uu___7 in
                       Prims.strcat "x_" uu___5 in
                     FStarC_SMTEncoding_Env.new_term_constant_from_string
                       env1 x uu___4 in
                   (match uu___3 with
                    | (xxsym, xx, env') ->
                        let t2 =
                          FStarC_SMTEncoding_Term.mk_HasTypeWithFuel
                            FStar_Pervasives_Native.None xx t in
                        let caption =
                          let uu___4 = FStarC_Options.log_queries () in
                          if uu___4
                          then
                            let uu___5 =
                              let uu___6 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_bv x in
                              let uu___7 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term
                                  x.FStarC_Syntax_Syntax.sort in
                              let uu___8 =
                                FStarC_Class_Show.show
                                  FStarC_Syntax_Print.showable_term t1 in
                              FStarC_Format.fmt3 "%s : %s (%s)" uu___6 uu___7
                                uu___8 in
                            FStar_Pervasives_Native.Some uu___5
                          else FStar_Pervasives_Native.None in
                        let ax =
                          let a_name = Prims.strcat "binder_" xxsym in
                          FStarC_SMTEncoding_Util.mkAssume
                            (t2, (FStar_Pervasives_Native.Some a_name),
                              a_name) in
                        let g =
                          let uu___4 =
                            FStarC_SMTEncoding_Term.mk_decls_trivial
                              [FStarC_SMTEncoding_Term.DeclFun
                                 (xxsym, [],
                                   FStarC_SMTEncoding_Term.Term_sort,
                                   caption)] in
                          let uu___5 =
                            let uu___6 =
                              FStarC_SMTEncoding_Term.mk_decls_trivial [ax] in
                            FStarC_List.op_At decls' uu___6 in
                          FStarC_List.op_At uu___4 uu___5 in
                        ((i + Prims.int_one), (FStarC_List.op_At decls g),
                          env'))))
         | FStarC_Syntax_Syntax.Binding_lid (x, (us, t)) ->
             let uu___1 = FStarC_Syntax_Subst.open_univ_vars us t in
             (match uu___1 with
              | (us1, t1) ->
                  let t_norm = norm_before_encoding env1 t1 in
                  let fv =
                    FStarC_Syntax_Syntax.lid_as_fv x
                      FStar_Pervasives_Native.None in
                  let uu___2 = encode_free_var false env1 fv us1 t1 t_norm [] in
                  (match uu___2 with
                   | (g, env') ->
                       ((i + Prims.int_one), (FStarC_List.op_At decls g),
                         env')))) in
  let uu___ =
    FStarC_List.fold_right encode_binding bindings (Prims.int_zero, [], env) in
  match uu___ with | (uu___1, decls, env1) -> (decls, env1)
let encode_labels (labs : FStarC_SMTEncoding_Term.error_label Prims.list) :
  (FStarC_SMTEncoding_Term.decl Prims.list * FStarC_SMTEncoding_Term.decl
    Prims.list)=
  let prefix =
    FStarC_List.map
      (fun uu___ ->
         match uu___ with
         | (l, uu___1, uu___2) ->
             let uu___3 =
               let uu___4 = FStarC_SMTEncoding_Term.fv_name l in
               (uu___4, [], FStarC_SMTEncoding_Term.Bool_sort,
                 FStar_Pervasives_Native.None) in
             FStarC_SMTEncoding_Term.DeclFun uu___3) labs in
  let suffix =
    FStarC_List.collect
      (fun uu___ ->
         match uu___ with
         | (l, uu___1, uu___2) ->
             let uu___3 =
               let uu___4 = FStarC_SMTEncoding_Term.fv_name l in
               FStarC_SMTEncoding_Term.Echo uu___4 in
             let uu___4 =
               let uu___5 =
                 let uu___6 = FStarC_SMTEncoding_Util.mkFreeV l in
                 FStarC_SMTEncoding_Term.Eval uu___6 in
               [uu___5] in
             uu___3 :: uu___4) labs in
  (prefix, suffix)
let last_env : FStarC_SMTEncoding_Env.env_t Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let init_env (tcenv : FStarC_TypeChecker_Env.env) : unit=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_PSMap.empty () in
      let uu___3 = let uu___4 = FStarC_PSMap.empty () in (uu___4, []) in
      let uu___4 =
        let uu___5 = FStarC_TypeChecker_Env.current_module tcenv in
        FStarC_Ident.string_of_lid uu___5 in
      let uu___5 = FStarC_SMap.create (Prims.of_int (100)) in
      {
        FStarC_SMTEncoding_Env.bvar_bindings = uu___2;
        FStarC_SMTEncoding_Env.fvar_bindings = uu___3;
        FStarC_SMTEncoding_Env.depth = Prims.int_zero;
        FStarC_SMTEncoding_Env.tcenv = tcenv;
        FStarC_SMTEncoding_Env.warn = true;
        FStarC_SMTEncoding_Env.nolabels = false;
        FStarC_SMTEncoding_Env.use_zfuel_name = false;
        FStarC_SMTEncoding_Env.encode_non_total_function_typ = true;
        FStarC_SMTEncoding_Env.current_module_name = uu___4;
        FStarC_SMTEncoding_Env.encoding_quantifier = false;
        FStarC_SMTEncoding_Env.global_cache = uu___5
      } in
    [uu___1] in
  FStarC_Effect.op_Colon_Equals last_env uu___
let get_env (cmn : FStarC_Ident.lident) (tcenv : FStarC_TypeChecker_Env.env)
  : FStarC_SMTEncoding_Env.env_t=
  let uu___ = FStarC_Effect.op_Bang last_env in
  match uu___ with
  | [] -> failwith "No env; call init first!"
  | e::uu___1 ->
      let uu___2 = FStarC_Ident.string_of_lid cmn in
      {
        FStarC_SMTEncoding_Env.bvar_bindings =
          (e.FStarC_SMTEncoding_Env.bvar_bindings);
        FStarC_SMTEncoding_Env.fvar_bindings =
          (e.FStarC_SMTEncoding_Env.fvar_bindings);
        FStarC_SMTEncoding_Env.depth = (e.FStarC_SMTEncoding_Env.depth);
        FStarC_SMTEncoding_Env.tcenv = tcenv;
        FStarC_SMTEncoding_Env.warn = (e.FStarC_SMTEncoding_Env.warn);
        FStarC_SMTEncoding_Env.nolabels = (e.FStarC_SMTEncoding_Env.nolabels);
        FStarC_SMTEncoding_Env.use_zfuel_name =
          (e.FStarC_SMTEncoding_Env.use_zfuel_name);
        FStarC_SMTEncoding_Env.encode_non_total_function_typ =
          (e.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
        FStarC_SMTEncoding_Env.current_module_name = uu___2;
        FStarC_SMTEncoding_Env.encoding_quantifier =
          (e.FStarC_SMTEncoding_Env.encoding_quantifier);
        FStarC_SMTEncoding_Env.global_cache =
          (e.FStarC_SMTEncoding_Env.global_cache)
      }
let set_env (env : FStarC_SMTEncoding_Env.env_t) : unit=
  let uu___ = FStarC_Effect.op_Bang last_env in
  match uu___ with
  | [] -> failwith "Empty env stack"
  | uu___1::tl -> FStarC_Effect.op_Colon_Equals last_env (env :: tl)
let get_current_env (tcenv : FStarC_TypeChecker_Env.env) :
  FStarC_SMTEncoding_Env.env_t=
  let uu___ = FStarC_TypeChecker_Env.current_module tcenv in
  get_env uu___ tcenv
let push_env (uu___ : unit) : unit=
  let uu___1 = FStarC_Effect.op_Bang last_env in
  match uu___1 with
  | [] -> failwith "Empty env stack"
  | hd::tl ->
      let top = copy_env hd in
      FStarC_Effect.op_Colon_Equals last_env (top :: hd :: tl)
let pop_env (uu___ : unit) : unit=
  let uu___1 = FStarC_Effect.op_Bang last_env in
  match uu___1 with
  | [] -> failwith "Popping an empty stack"
  | uu___2::tl -> FStarC_Effect.op_Colon_Equals last_env tl
let snapshot_env (uu___ : unit) : (Prims.int * unit)=
  FStarC_Common.snapshot "SMTEncoding.Encode.env" push_env last_env ()
let rollback_env (depth : Prims.int FStar_Pervasives_Native.option) : 
  unit=
  FStarC_Common.rollback "SMTEncoding.Encode.env" pop_env last_env depth
let init (tcenv : FStarC_TypeChecker_Env.env) : unit=
  init_env tcenv;
  FStarC_SMTEncoding_Z3.giveZ3 [FStarC_SMTEncoding_Term.DefPrelude]
let snapshot_encoding (msg : Prims.string) : encoding_depth=
  FStarC_Util.atomically
    (fun uu___ ->
       (let uu___2 = FStarC_Debug.medium () in
        if uu___2
        then FStarC_Format.print1 "Encode.snapshot_encoding: %s\n" msg
        else ());
       (let uu___2 = snapshot_env () in
        match uu___2 with
        | (env_depth, ()) ->
            let uu___3 =
              FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.snapshot
                () in
            (match uu___3 with
             | (varops_depth, ()) -> (env_depth, varops_depth))))
let rollback_encoding (msg : Prims.string)
  (depth : encoding_depth FStar_Pervasives_Native.option) : unit=
  FStarC_Util.atomically
    (fun uu___ ->
       (let uu___2 = FStarC_Debug.medium () in
        if uu___2
        then
          let uu___3 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_option
                 (FStarC_Class_Show.show_tuple2
                    FStarC_Class_Show.showable_int
                    FStarC_Class_Show.showable_int)) depth in
          FStarC_Format.print2 "Encode.rollback_encoding: %s to %s\n" msg
            uu___3
        else ());
       (let uu___2 =
          match depth with
          | FStar_Pervasives_Native.Some (s1, s2) ->
              ((FStar_Pervasives_Native.Some s1),
                (FStar_Pervasives_Native.Some s2))
          | FStar_Pervasives_Native.None ->
              (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) in
        match uu___2 with
        | (env_depth, varops_depth) ->
            (rollback_env env_depth;
             FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.rollback
               varops_depth)))
let push_encoding_state (msg : Prims.string) : unit=
  let uu___ = snapshot_encoding msg in ()
let pop_encoding_state (msg : Prims.string) : unit=
  rollback_encoding msg FStar_Pervasives_Native.None
let open_fact_db_tags (env : FStarC_SMTEncoding_Env.env_t) :
  FStarC_SMTEncoding_Term.fact_db_id Prims.list= []
let place_decl_in_fact_dbs (env : FStarC_SMTEncoding_Env.env_t)
  (fact_db_ids : FStarC_SMTEncoding_Term.fact_db_id Prims.list)
  (d : FStarC_SMTEncoding_Term.decl) : FStarC_SMTEncoding_Term.decl=
  match (fact_db_ids, d) with
  | (uu___::uu___1, FStarC_SMTEncoding_Term.Assume a) ->
      FStarC_SMTEncoding_Term.Assume
        {
          FStarC_SMTEncoding_Term.assumption_term =
            (a.FStarC_SMTEncoding_Term.assumption_term);
          FStarC_SMTEncoding_Term.assumption_caption =
            (a.FStarC_SMTEncoding_Term.assumption_caption);
          FStarC_SMTEncoding_Term.assumption_name =
            (a.FStarC_SMTEncoding_Term.assumption_name);
          FStarC_SMTEncoding_Term.assumption_fact_ids = fact_db_ids;
          FStarC_SMTEncoding_Term.assumption_free_names =
            (a.FStarC_SMTEncoding_Term.assumption_free_names)
        }
  | uu___ -> d
let place_decl_elt_in_fact_dbs (env : FStarC_SMTEncoding_Env.env_t)
  (fact_db_ids : FStarC_SMTEncoding_Term.fact_db_id Prims.list)
  (elt : FStarC_SMTEncoding_Term.decls_elt) :
  FStarC_SMTEncoding_Term.decls_elt=
  let uu___ =
    FStarC_List.map (place_decl_in_fact_dbs env fact_db_ids)
      elt.FStarC_SMTEncoding_Term.decls in
  {
    FStarC_SMTEncoding_Term.sym_name = (elt.FStarC_SMTEncoding_Term.sym_name);
    FStarC_SMTEncoding_Term.key = (elt.FStarC_SMTEncoding_Term.key);
    FStarC_SMTEncoding_Term.decls = uu___;
    FStarC_SMTEncoding_Term.a_names = (elt.FStarC_SMTEncoding_Term.a_names)
  }
let fact_dbs_for_lid (env : FStarC_SMTEncoding_Env.env_t)
  (lid : FStarC_Ident.lid) : FStarC_SMTEncoding_Term.fact_db_id Prims.list=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Ident.ns_of_lid lid in
        FStarC_Ident.lid_of_ids uu___3 in
      FStarC_SMTEncoding_Term.Namespace uu___2 in
    let uu___2 = open_fact_db_tags env in uu___1 :: uu___2 in
  (FStarC_SMTEncoding_Term.Name lid) :: uu___
let encode_top_level_facts (env : FStarC_SMTEncoding_Env.env_t)
  (se : FStarC_Syntax_Syntax.sigelt) :
  (FStarC_SMTEncoding_Term.decls_elt Prims.list *
    FStarC_SMTEncoding_Env.env_t)=
  let fact_db_ids =
    let uu___ = FStarC_Syntax_Util.lids_of_sigelt se in
    FStarC_List.collect (fact_dbs_for_lid env) uu___ in
  let uu___ = encode_sigelt env se in
  match uu___ with
  | (g, env1) ->
      let g1 =
        FStarC_List.map (place_decl_elt_in_fact_dbs env1 fact_db_ids) g in
      (g1, env1)
let recover_caching_and_update_env (env : FStarC_SMTEncoding_Env.env_t)
  (decls : FStarC_SMTEncoding_Term.decls_t) :
  FStarC_SMTEncoding_Term.decls_t=
  FStarC_List.collect
    (fun elt ->
       if elt.FStarC_SMTEncoding_Term.key = FStar_Pervasives_Native.None
       then [elt]
       else
         (let uu___1 =
            FStarC_SMap.try_find env.FStarC_SMTEncoding_Env.global_cache
              (FStar_Pervasives_Native.__proj__Some__item__v
                 elt.FStarC_SMTEncoding_Term.key) in
          match uu___1 with
          | FStar_Pervasives_Native.Some (cache_elt, uu___2) ->
              FStarC_SMTEncoding_Term.mk_decls_trivial
                [FStarC_SMTEncoding_Term.RetainAssumptions
                   (cache_elt.FStarC_SMTEncoding_Term.a_names)]
          | FStar_Pervasives_Native.None ->
              ((let uu___3 =
                  let uu___4 =
                    FStarC_TypeChecker_Env.current_module
                      env.FStarC_SMTEncoding_Env.tcenv in
                  (elt, uu___4) in
                FStarC_SMap.add env.FStarC_SMTEncoding_Env.global_cache
                  (FStar_Pervasives_Native.__proj__Some__item__v
                     elt.FStarC_SMTEncoding_Term.key) uu___3);
               [elt]))) decls
let encode_sig (tcenv : FStarC_TypeChecker_Env.env)
  (se : FStarC_Syntax_Syntax.sigelt) : unit=
  FStarC_Stats.record "encode_sig"
    (fun uu___ ->
       let caption decls =
         let uu___1 = FStarC_Options.log_queries () in
         if uu___1
         then
           let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_Syntax_Print.sigelt_to_string_short se in
               Prims.strcat "encoding sigelt " uu___4 in
             FStarC_SMTEncoding_Term.Caption uu___3 in
           uu___2 :: decls
         else decls in
       (let uu___2 = FStarC_Debug.medium () in
        if uu___2
        then
          let uu___3 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_sigelt se in
          FStarC_Format.print1 "+++++++++++Encoding sigelt %s\n" uu___3
        else ());
       (let env =
          let uu___2 = FStarC_TypeChecker_Env.current_module tcenv in
          get_env uu___2 tcenv in
        let uu___2 = encode_top_level_facts env se in
        match uu___2 with
        | (decls, env1) ->
            (set_env env1;
             (let uu___4 =
                let uu___5 =
                  let uu___6 = recover_caching_and_update_env env1 decls in
                  FStarC_SMTEncoding_Term.decls_list_of uu___6 in
                caption uu___5 in
              FStarC_SMTEncoding_Z3.giveZ3 uu___4))))
let give_decls_to_z3_and_set_env (env : FStarC_SMTEncoding_Env.env_t)
  (name : Prims.string) (decls : FStarC_SMTEncoding_Term.decls_t) : unit=
  let caption decls1 =
    let uu___ = FStarC_Options.log_queries () in
    if uu___
    then
      let msg = Prims.strcat "Externals for " name in
      [FStarC_SMTEncoding_Term.Module
         (name,
           (FStarC_List.op_At ((FStarC_SMTEncoding_Term.Caption msg) ::
              decls1)
              [FStarC_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]))]
    else [FStarC_SMTEncoding_Term.Module (name, decls1)] in
  set_env
    {
      FStarC_SMTEncoding_Env.bvar_bindings =
        (env.FStarC_SMTEncoding_Env.bvar_bindings);
      FStarC_SMTEncoding_Env.fvar_bindings =
        (env.FStarC_SMTEncoding_Env.fvar_bindings);
      FStarC_SMTEncoding_Env.depth = (env.FStarC_SMTEncoding_Env.depth);
      FStarC_SMTEncoding_Env.tcenv = (env.FStarC_SMTEncoding_Env.tcenv);
      FStarC_SMTEncoding_Env.warn = true;
      FStarC_SMTEncoding_Env.nolabels = (env.FStarC_SMTEncoding_Env.nolabels);
      FStarC_SMTEncoding_Env.use_zfuel_name =
        (env.FStarC_SMTEncoding_Env.use_zfuel_name);
      FStarC_SMTEncoding_Env.encode_non_total_function_typ =
        (env.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
      FStarC_SMTEncoding_Env.current_module_name =
        (env.FStarC_SMTEncoding_Env.current_module_name);
      FStarC_SMTEncoding_Env.encoding_quantifier =
        (env.FStarC_SMTEncoding_Env.encoding_quantifier);
      FStarC_SMTEncoding_Env.global_cache =
        (env.FStarC_SMTEncoding_Env.global_cache)
    };
  (let z3_decls =
     let uu___1 =
       let uu___2 = recover_caching_and_update_env env decls in
       FStarC_SMTEncoding_Term.decls_list_of uu___2 in
     caption uu___1 in
   FStarC_SMTEncoding_Z3.giveZ3 z3_decls)
let instance_showable_smap (uu___ : 'a FStarC_Class_Show.showable) :
  'a FStarC_SMap.t FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun smap ->
         FStarC_SMap.fold smap
           (fun k v acc ->
              let uu___1 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_string k in
              let uu___2 = FStarC_Class_Show.show uu___ v in
              FStarC_Format.fmt3 "%s -> %s\n%s" uu___1 uu___2 acc) "")
  }
let encode_modul (tcenv : FStarC_TypeChecker_Env.env)
  (modul : FStarC_Syntax_Syntax.modul) :
  (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.fvar_binding
    Prims.list)=
  let uu___ = (FStarC_Options.lax ()) && (FStarC_Options.ml_ish ()) in
  if uu___
  then ([], [])
  else
    (let tcenv1 =
       FStarC_TypeChecker_Env.set_current_module tcenv
         modul.FStarC_Syntax_Syntax.name in
     FStarC_Syntax_Unionfind.with_uf_enabled
       (fun uu___2 ->
          FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.reset_fresh ();
          (let name =
             let uu___4 =
               FStarC_Ident.string_of_lid modul.FStarC_Syntax_Syntax.name in
             FStarC_Format.fmt2 "%s %s"
               (if modul.FStarC_Syntax_Syntax.is_interface
                then "interface"
                else "module") uu___4 in
           (let uu___5 = FStarC_Debug.medium () in
            if uu___5
            then
              let uu___6 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                  (FStarC_List.length modul.FStarC_Syntax_Syntax.declarations) in
              FStarC_Format.print2
                "+++++++++++Encoding externals for %s ... %s declarations\n"
                name uu___6
            else ());
           (let env =
              let uu___5 = get_env modul.FStarC_Syntax_Syntax.name tcenv1 in
              FStarC_SMTEncoding_Env.reset_current_module_fvbs uu___5 in
            let clear_current_module env1 =
              let keys =
                FStarC_SMap.keys env1.FStarC_SMTEncoding_Env.global_cache in
              FStarC_List.iter
                (fun k ->
                   let uu___6 =
                     FStarC_SMap.try_find
                       env1.FStarC_SMTEncoding_Env.global_cache k in
                   match uu___6 with
                   | FStar_Pervasives_Native.None -> ()
                   | FStar_Pervasives_Native.Some (elts, m) ->
                       let uu___7 =
                         FStarC_Ident.lid_equals m
                           modul.FStarC_Syntax_Syntax.name in
                       if uu___7
                       then
                         FStarC_SMap.remove
                           env1.FStarC_SMTEncoding_Env.global_cache k
                       else ()) keys;
              (let fvb =
                 let uu___6 = FStarC_PSMap.empty () in
                 FStarC_PSMap.fold
                   (FStar_Pervasives_Native.fst
                      env1.FStarC_SMTEncoding_Env.fvar_bindings)
                   (fun key v fvb1 ->
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            FStarC_Ident.ns_of_lid
                              v.FStarC_SMTEncoding_Env.fvar_lid in
                          FStarC_Ident.lid_of_ids uu___9 in
                        FStarC_Ident.lid_equals uu___8
                          modul.FStarC_Syntax_Syntax.name in
                      if uu___7 then fvb1 else FStarC_PSMap.add fvb1 key v)
                   uu___6 in
               (let uu___7 =
                  let uu___8 = FStarC_Options.interactive () in
                  Prims.op_Negation uu___8 in
                if uu___7
                then
                  FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.reset_scope
                    ()
                else ());
               {
                 FStarC_SMTEncoding_Env.bvar_bindings =
                   (env1.FStarC_SMTEncoding_Env.bvar_bindings);
                 FStarC_SMTEncoding_Env.fvar_bindings = (fvb, []);
                 FStarC_SMTEncoding_Env.depth =
                   (env1.FStarC_SMTEncoding_Env.depth);
                 FStarC_SMTEncoding_Env.tcenv =
                   (env1.FStarC_SMTEncoding_Env.tcenv);
                 FStarC_SMTEncoding_Env.warn =
                   (env1.FStarC_SMTEncoding_Env.warn);
                 FStarC_SMTEncoding_Env.nolabels =
                   (env1.FStarC_SMTEncoding_Env.nolabels);
                 FStarC_SMTEncoding_Env.use_zfuel_name =
                   (env1.FStarC_SMTEncoding_Env.use_zfuel_name);
                 FStarC_SMTEncoding_Env.encode_non_total_function_typ =
                   (env1.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
                 FStarC_SMTEncoding_Env.current_module_name =
                   (env1.FStarC_SMTEncoding_Env.current_module_name);
                 FStarC_SMTEncoding_Env.encoding_quantifier =
                   (env1.FStarC_SMTEncoding_Env.encoding_quantifier);
                 FStarC_SMTEncoding_Env.global_cache =
                   (env1.FStarC_SMTEncoding_Env.global_cache)
               }) in
            let env1 =
              let uu___5 = FStarC_Parser_Dep.fly_deps_enabled () in
              if uu___5 then clear_current_module env else env in
            (let uu___6 = FStarC_Debug.high () in
             if uu___6
             then
               let uu___7 =
                 let uu___8 =
                   FStarC_SMap.size env1.FStarC_SMTEncoding_Env.global_cache in
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___8 in
               let uu___8 =
                 FStarC_Class_Show.show
                   (instance_showable_smap
                      (FStarC_Class_Show.show_tuple2
                         FStarC_SMTEncoding_Term.showable_decls_elt
                         FStarC_Ident.showable_lident))
                   env1.FStarC_SMTEncoding_Env.global_cache in
               let uu___9 = FStarC_SMTEncoding_Env.print_env env1 in
               FStarC_Format.print3
                 "Global cache contains %s entries\n{%s}\nenv={%s}" uu___7
                 uu___8 uu___9
             else ());
            (let encode_signature env2 ses =
               let uu___6 =
                 FStarC_List.fold_left
                   (fun uu___7 se ->
                      match uu___7 with
                      | (g, env3) ->
                          let uu___8 = encode_top_level_facts env3 se in
                          (match uu___8 with
                           | (g', env4) ->
                               ((FStarC_List.rev_append g' g), env4)))
                   ([], env2) ses in
               match uu___6 with | (g', env3) -> ((FStarC_List.rev g'), env3) in
             let uu___6 =
               encode_signature
                 {
                   FStarC_SMTEncoding_Env.bvar_bindings =
                     (env1.FStarC_SMTEncoding_Env.bvar_bindings);
                   FStarC_SMTEncoding_Env.fvar_bindings =
                     (env1.FStarC_SMTEncoding_Env.fvar_bindings);
                   FStarC_SMTEncoding_Env.depth =
                     (env1.FStarC_SMTEncoding_Env.depth);
                   FStarC_SMTEncoding_Env.tcenv =
                     (env1.FStarC_SMTEncoding_Env.tcenv);
                   FStarC_SMTEncoding_Env.warn = false;
                   FStarC_SMTEncoding_Env.nolabels =
                     (env1.FStarC_SMTEncoding_Env.nolabels);
                   FStarC_SMTEncoding_Env.use_zfuel_name =
                     (env1.FStarC_SMTEncoding_Env.use_zfuel_name);
                   FStarC_SMTEncoding_Env.encode_non_total_function_typ =
                     (env1.FStarC_SMTEncoding_Env.encode_non_total_function_typ);
                   FStarC_SMTEncoding_Env.current_module_name =
                     (env1.FStarC_SMTEncoding_Env.current_module_name);
                   FStarC_SMTEncoding_Env.encoding_quantifier =
                     (env1.FStarC_SMTEncoding_Env.encoding_quantifier);
                   FStarC_SMTEncoding_Env.global_cache =
                     (env1.FStarC_SMTEncoding_Env.global_cache)
                 } modul.FStarC_Syntax_Syntax.declarations in
             match uu___6 with
             | (decls, env2) ->
                 (give_decls_to_z3_and_set_env env2 name decls;
                  (let uu___9 = FStarC_Debug.medium () in
                   if uu___9
                   then
                     FStarC_Format.print1 "Done encoding externals for %s\n"
                       name
                   else ());
                  (decls,
                    (FStarC_SMTEncoding_Env.get_current_module_fvbs env2))))))))
let encode_modul_from_cache (tcenv : FStarC_TypeChecker_Env.env)
  (tcmod : FStarC_Syntax_Syntax.modul)
  (uu___ :
    (FStarC_SMTEncoding_Term.decls_t * FStarC_SMTEncoding_Env.fvar_binding
      Prims.list))
  : unit=
  match uu___ with
  | (decls, fvbs) ->
      let uu___1 = (FStarC_Options.lax ()) && (FStarC_Options.ml_ish ()) in
      if uu___1
      then ()
      else
        (let tcenv1 =
           FStarC_TypeChecker_Env.set_current_module tcenv
             tcmod.FStarC_Syntax_Syntax.name in
         let name =
           let uu___3 =
             FStarC_Ident.string_of_lid tcmod.FStarC_Syntax_Syntax.name in
           FStarC_Format.fmt2 "%s %s"
             (if tcmod.FStarC_Syntax_Syntax.is_interface
              then "interface"
              else "module") uu___3 in
         (let uu___4 = FStarC_Debug.medium () in
          if uu___4
          then
            let uu___5 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                (FStarC_List.length decls) in
            FStarC_Format.print2
              "+++++++++++Encoding externals from cache for %s ... %s decls\n"
              name uu___5
          else ());
         (let env =
            let uu___4 = get_env tcmod.FStarC_Syntax_Syntax.name tcenv1 in
            FStarC_SMTEncoding_Env.reset_current_module_fvbs uu___4 in
          let env1 =
            FStarC_List.fold_left
              (fun env2 fvb ->
                 FStarC_SMTEncoding_Env.add_fvar_binding_to_env fvb env2) env
              (FStarC_List.rev fvbs) in
          give_decls_to_z3_and_set_env env1 name decls;
          (let uu___5 = FStarC_Debug.medium () in
           if uu___5
           then
             FStarC_Format.print1
               "Done encoding externals from cache for %s\n" name
           else ())))
let encode_query
  (use_env_msg : (unit -> Prims.string) FStar_Pervasives_Native.option)
  (tcenv : FStarC_TypeChecker_Env.env) (q : FStarC_Syntax_Syntax.term) :
  (FStarC_SMTEncoding_Term.decl Prims.list *
    FStarC_SMTEncoding_ErrorReporting.label Prims.list *
    FStarC_SMTEncoding_Term.decl * FStarC_SMTEncoding_Term.decl Prims.list)=
  FStarC_Errors.with_ctx "While encoding a query"
    (fun uu___ ->
       (let uu___2 =
          let uu___3 = FStarC_TypeChecker_Env.current_module tcenv in
          FStarC_Ident.string_of_lid uu___3 in
        FStarC_SMTEncoding_Z3.query_logging.FStarC_SMTEncoding_Z3.set_module_name
          uu___2);
       (let env =
          let uu___2 = FStarC_TypeChecker_Env.current_module tcenv in
          get_env uu___2 tcenv in
        let uu___2 =
          let rec aux bindings =
            match bindings with
            | (FStarC_Syntax_Syntax.Binding_var x)::rest ->
                let uu___3 = aux rest in
                (match uu___3 with
                 | (out, rest1) ->
                     let t =
                       let uu___4 =
                         FStarC_Syntax_Formula.destruct_typ_as_formula
                           x.FStarC_Syntax_Syntax.sort in
                       match uu___4 with
                       | FStar_Pervasives_Native.Some uu___5 ->
                           let uu___6 =
                             FStarC_Syntax_Syntax.new_bv
                               FStar_Pervasives_Native.None
                               FStarC_Syntax_Syntax.t_unit in
                           FStarC_Syntax_Util.refine uu___6
                             x.FStarC_Syntax_Syntax.sort
                       | uu___5 -> x.FStarC_Syntax_Syntax.sort in
                     let t1 =
                       norm_with_steps
                         [FStarC_TypeChecker_Env.Eager_unfolding;
                         FStarC_TypeChecker_Env.Beta;
                         FStarC_TypeChecker_Env.Simplify;
                         FStarC_TypeChecker_Env.Primops]
                         env.FStarC_SMTEncoding_Env.tcenv t in
                     let uu___4 =
                       let uu___5 =
                         FStarC_Syntax_Syntax.mk_binder
                           {
                             FStarC_Syntax_Syntax.ppname =
                               (x.FStarC_Syntax_Syntax.ppname);
                             FStarC_Syntax_Syntax.index =
                               (x.FStarC_Syntax_Syntax.index);
                             FStarC_Syntax_Syntax.sort = t1
                           } in
                       uu___5 :: out in
                     (uu___4, rest1))
            | uu___3 -> ([], bindings) in
          let uu___3 = aux tcenv.FStarC_TypeChecker_Env.gamma in
          match uu___3 with
          | (closing, bindings) ->
              let uu___4 =
                FStarC_Syntax_Util.close_forall_no_univs
                  (FStarC_List.rev closing) q in
              (uu___4, bindings) in
        match uu___2 with
        | (q1, bindings) ->
            let uu___3 = encode_env_bindings env bindings in
            (match uu___3 with
             | (env_decls, env1) ->
                 ((let uu___5 =
                     (FStarC_Debug.medium ()) ||
                       (FStarC_Effect.op_Bang dbg_SMTEncoding) in
                   if uu___5
                   then
                     let uu___6 =
                       FStarC_Class_Show.show
                         FStarC_Syntax_Print.showable_term q1 in
                     FStarC_Format.print1 "Encoding query formula {: %s\n"
                       uu___6
                   else ());
                  (let uu___5 =
                     FStarC_Timing.record_ms
                       (fun uu___6 ->
                          FStarC_SMTEncoding_EncodeTerm.encode_formula q1
                            env1) in
                   match uu___5 with
                   | ((phi, qdecls), ms) ->
                       let uu___6 =
                         let uu___7 = FStarC_TypeChecker_Env.get_range tcenv in
                         FStarC_SMTEncoding_ErrorReporting.label_goals
                           use_env_msg uu___7 phi in
                       (match uu___6 with
                        | (labels, phi1) ->
                            let uu___7 = encode_labels labels in
                            (match uu___7 with
                             | (label_prefix, label_suffix) ->
                                 let caption =
                                   let uu___8 =
                                     (FStarC_Options.log_queries ()) ||
                                       (FStarC_Options.log_failing_queries ()) in
                                   if uu___8
                                   then
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           FStarC_Class_Show.show
                                             FStarC_Syntax_Print.showable_term
                                             q1 in
                                         Prims.strcat
                                           "Encoding query formula : "
                                           uu___11 in
                                       FStarC_SMTEncoding_Term.Caption
                                         uu___10 in
                                     let uu___10 =
                                       let uu___11 =
                                         let uu___12 =
                                           let uu___13 =
                                             let uu___14 =
                                               FStarC_Errors.get_ctx () in
                                             FStarC_String.concat "\n"
                                               uu___14 in
                                           Prims.strcat "Context: " uu___13 in
                                         FStarC_SMTEncoding_Term.Caption
                                           uu___12 in
                                       [uu___11] in
                                     uu___9 :: uu___10
                                   else [] in
                                 let query_prelude =
                                   let uu___8 =
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           FStarC_SMTEncoding_Term.mk_decls_trivial
                                             label_prefix in
                                         let uu___12 =
                                           let uu___13 =
                                             FStarC_SMTEncoding_Term.mk_decls_trivial
                                               caption in
                                           FStarC_List.op_At qdecls uu___13 in
                                         FStarC_List.op_At uu___11 uu___12 in
                                       FStarC_List.op_At env_decls uu___10 in
                                     recover_caching_and_update_env env1
                                       uu___9 in
                                   FStarC_SMTEncoding_Term.decls_list_of
                                     uu___8 in
                                 let qry =
                                   let uu___8 =
                                     let uu___9 =
                                       FStarC_SMTEncoding_Util.mkNot phi1 in
                                     let uu___10 =
                                       FStarC_SMTEncoding_Env.varops.FStarC_SMTEncoding_Env.mk_unique
                                         "@query" in
                                     (uu___9,
                                       (FStar_Pervasives_Native.Some "query"),
                                       uu___10) in
                                   FStarC_SMTEncoding_Util.mkAssume uu___8 in
                                 let suffix =
                                   FStarC_List.op_At
                                     [FStarC_SMTEncoding_Term.Echo "<labels>"]
                                     (FStarC_List.op_At label_suffix
                                        [FStarC_SMTEncoding_Term.Echo
                                           "</labels>";
                                        FStarC_SMTEncoding_Term.Echo "Done!"]) in
                                 ((let uu___9 =
                                     (FStarC_Debug.medium ()) ||
                                       (FStarC_Effect.op_Bang dbg_SMTEncoding) in
                                   if uu___9
                                   then
                                     FStarC_Format.print_string
                                       "} Done encoding\n"
                                   else ());
                                  (let uu___10 =
                                     ((FStarC_Debug.medium ()) ||
                                        (FStarC_Effect.op_Bang
                                           dbg_SMTEncoding))
                                       || (FStarC_Effect.op_Bang dbg_Time) in
                                   if uu___10
                                   then
                                     let uu___11 =
                                       FStarC_Class_Show.show
                                         FStarC_Class_Show.showable_int ms in
                                     FStarC_Format.print1
                                       "Encoding took %sms\n" uu___11
                                   else ());
                                  (query_prelude, labels, qry, suffix)))))))))
