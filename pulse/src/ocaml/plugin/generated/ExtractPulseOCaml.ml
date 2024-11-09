open Prims
let (dbg : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "extraction"
let (hua :
  FStarC_Syntax_Syntax.term ->
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universe Prims.list *
      FStarC_Syntax_Syntax.args) FStar_Pervasives_Native.option)
  =
  fun t ->
    let t1 = FStarC_Syntax_Util.unmeta t in
    let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
    match uu___ with
    | (hd, args) ->
        let hd1 = FStarC_Syntax_Util.unmeta hd in
        let uu___1 =
          let uu___2 = FStarC_Syntax_Subst.compress hd1 in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             FStar_Pervasives_Native.Some (fv, [], args)
         | FStarC_Syntax_Syntax.Tm_uinst
             ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar fv;
                FStarC_Syntax_Syntax.pos = uu___2;
                FStarC_Syntax_Syntax.vars = uu___3;
                FStarC_Syntax_Syntax.hash_code = uu___4;_},
              us)
             -> FStar_Pervasives_Native.Some (fv, us, args)
         | uu___2 -> FStar_Pervasives_Native.None)
let (tr_typ :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.term -> FStarC_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t ->
      (let uu___1 =
         let uu___2 = FStarC_Options_Ext.get "pulse:extract_ocaml_bare" in
         uu___2 = "" in
       if uu___1
       then
         FStarC_Compiler_Effect.raise
           FStarC_Extraction_ML_Term.NotSupportedByExtension
       else ());
      (let cb = FStarC_Extraction_ML_Term.term_as_mlty in
       let hua1 = hua t in
       if FStar_Pervasives_Native.uu___is_None hua1
       then
         FStarC_Compiler_Effect.raise
           FStarC_Extraction_ML_Term.NotSupportedByExtension
       else ();
       (let uu___2 = hua1 in
        match uu___2 with
        | FStar_Pervasives_Native.Some (fv, us, args) ->
            (match (fv, us, args) with
             | (uu___3, uu___4, (t1, uu___5)::[]) when
                 let uu___6 =
                   FStarC_Ident.lid_of_str "Pulse.Lib.Array.Core.array" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let uu___6 =
                   let uu___7 = let uu___8 = cb g t1 in [uu___8] in
                   (uu___7, ([], "array")) in
                 FStarC_Extraction_ML_Syntax.MLTY_Named uu___6
             | (uu___3, uu___4, (t1, uu___5)::[]) when
                 let uu___6 =
                   FStarC_Ident.lid_of_str "Pulse.Lib.Reference.ref" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let uu___6 =
                   let uu___7 = let uu___8 = cb g t1 in [uu___8] in
                   (uu___7, ([], "ref")) in
                 FStarC_Extraction_ML_Syntax.MLTY_Named uu___6
             | (uu___3, uu___4, []) when
                 let uu___5 = FStarC_Ident.lid_of_str "FStar.SizeT.t" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___5 ->
                 FStarC_Extraction_ML_Syntax.MLTY_Named ([], ([], "int"))
             | (uu___3, uu___4, []) when
                 let uu___5 = FStarC_Ident.lid_of_str "Prims.nat" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___5 ->
                 FStarC_Extraction_ML_Syntax.MLTY_Named ([], ([], "int"))
             | (uu___3, uu___4, []) when
                 let uu___5 = FStarC_Ident.lid_of_str "Prims.int" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___5 ->
                 FStarC_Extraction_ML_Syntax.MLTY_Named ([], ([], "int"))
             | uu___3 ->
                 FStarC_Compiler_Effect.raise
                   FStarC_Extraction_ML_Term.NotSupportedByExtension)))
let (tr_expr :
  FStarC_Extraction_ML_UEnv.uenv ->
    FStarC_Syntax_Syntax.term ->
      (FStarC_Extraction_ML_Syntax.mlexpr * FStarC_Extraction_ML_Syntax.e_tag
        * FStarC_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun t ->
      (let uu___1 =
         let uu___2 = FStarC_Options_Ext.get "pulse:extract_ocaml_bare" in
         uu___2 = "" in
       if uu___1
       then
         FStarC_Compiler_Effect.raise
           FStarC_Extraction_ML_Term.NotSupportedByExtension
       else ());
      (let cb = FStarC_Extraction_ML_Term.term_as_mlexpr in
       let hua1 = hua t in
       if FStar_Pervasives_Native.uu___is_None hua1
       then
         FStarC_Compiler_Effect.raise
           FStarC_Extraction_ML_Term.NotSupportedByExtension
       else ();
       (let uu___2 = hua1 in
        match uu___2 with
        | FStar_Pervasives_Native.Some (fv, us, args) ->
            (match (fv, us, args) with
             | (uu___3, uu___4, (x, uu___5)::[]) when
                 let uu___6 = FStarC_Ident.lid_of_str "FStar.SizeT.uint_to_t" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 -> cb g x
             | (uu___3, uu___4,
                (t1, uu___5)::(v0, FStar_Pervasives_Native.None)::[]) when
                 let uu___6 =
                   FStarC_Ident.lid_of_str "Pulse.Lib.Reference.alloc" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let mlty = FStarC_Extraction_ML_Term.term_as_mlty g t1 in
                 let bang =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.ml_unit_ty
                     (FStarC_Extraction_ML_Syntax.MLE_Var "ref") in
                 let e =
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           let uu___10 = cb g v0 in
                           FStar_Pervasives_Native.__proj__Mktuple3__item___1
                             uu___10 in
                         [uu___9] in
                       (bang, uu___8) in
                     FStarC_Extraction_ML_Syntax.MLE_App uu___7 in
                   FStarC_Extraction_ML_Syntax.with_ty mlty uu___6 in
                 (e, FStarC_Extraction_ML_Syntax.E_PURE, mlty)
             | (uu___3, uu___4,
                (t1, uu___5)::(v0, FStar_Pervasives_Native.None)::[]) when
                 let uu___6 =
                   FStarC_Ident.lid_of_str "Pulse.Lib.Reference.free" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 (FStarC_Extraction_ML_Syntax.ml_unit,
                   FStarC_Extraction_ML_Syntax.E_PURE,
                   FStarC_Extraction_ML_Syntax.ml_unit_ty)
             | (uu___3, uu___4,
                (t1, uu___5)::(r, FStar_Pervasives_Native.None)::_n::_p::[])
                 when
                 let uu___6 =
                   FStarC_Ident.lid_of_str "Pulse.Lib.Reference.op_Bang" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let mlty = FStarC_Extraction_ML_Term.term_as_mlty g t1 in
                 let bang =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.ml_unit_ty
                     (FStarC_Extraction_ML_Syntax.MLE_Var "!") in
                 let e =
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           let uu___10 = cb g r in
                           FStar_Pervasives_Native.__proj__Mktuple3__item___1
                             uu___10 in
                         [uu___9] in
                       (bang, uu___8) in
                     FStarC_Extraction_ML_Syntax.MLE_App uu___7 in
                   FStarC_Extraction_ML_Syntax.with_ty mlty uu___6 in
                 (e, FStarC_Extraction_ML_Syntax.E_PURE, mlty)
             | (uu___3, uu___4,
                (t1, uu___5)::(r, FStar_Pervasives_Native.None)::(x,
                                                                  FStar_Pervasives_Native.None)::_n::[])
                 when
                 let uu___6 =
                   FStarC_Ident.lid_of_str
                     "Pulse.Lib.Reference.op_Colon_Equals" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let mlty = FStarC_Extraction_ML_Term.term_as_mlty g t1 in
                 let bang =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.ml_unit_ty
                     (FStarC_Extraction_ML_Syntax.MLE_Var "(:=)") in
                 let e =
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           let uu___10 = cb g r in
                           FStar_Pervasives_Native.__proj__Mktuple3__item___1
                             uu___10 in
                         let uu___10 =
                           let uu___11 =
                             let uu___12 = cb g x in
                             FStar_Pervasives_Native.__proj__Mktuple3__item___1
                               uu___12 in
                           [uu___11] in
                         uu___9 :: uu___10 in
                       (bang, uu___8) in
                     FStarC_Extraction_ML_Syntax.MLE_App uu___7 in
                   FStarC_Extraction_ML_Syntax.with_ty mlty uu___6 in
                 (e, FStarC_Extraction_ML_Syntax.E_PURE, mlty)
             | (uu___3, uu___4,
                (t1, uu___5)::(x, FStar_Pervasives_Native.None)::(sz,
                                                                  FStar_Pervasives_Native.None)::[])
                 when
                 let uu___6 =
                   FStarC_Ident.lid_of_str "Pulse.Lib.Array.Core.alloc" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let mlty = FStarC_Extraction_ML_Term.term_as_mlty g t1 in
                 let bang =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.ml_unit_ty
                     (FStarC_Extraction_ML_Syntax.MLE_Var "Array.make") in
                 let e =
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           let uu___10 = cb g sz in
                           FStar_Pervasives_Native.__proj__Mktuple3__item___1
                             uu___10 in
                         let uu___10 =
                           let uu___11 =
                             let uu___12 = cb g x in
                             FStar_Pervasives_Native.__proj__Mktuple3__item___1
                               uu___12 in
                           [uu___11] in
                         uu___9 :: uu___10 in
                       (bang, uu___8) in
                     FStarC_Extraction_ML_Syntax.MLE_App uu___7 in
                   FStarC_Extraction_ML_Syntax.with_ty mlty uu___6 in
                 (e, FStarC_Extraction_ML_Syntax.E_PURE, mlty)
             | (uu___3, uu___4,
                (t1, uu___5)::(a, FStar_Pervasives_Native.None)::(i,
                                                                  FStar_Pervasives_Native.None)::_p::_s::[])
                 when
                 let uu___6 =
                   FStarC_Ident.lid_of_str
                     "Pulse.Lib.Array.Core.op_Array_Access" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let mlty = FStarC_Extraction_ML_Term.term_as_mlty g t1 in
                 let bang =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.ml_unit_ty
                     (FStarC_Extraction_ML_Syntax.MLE_Var "Array.get") in
                 let a1 =
                   let uu___6 = cb g a in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let i1 =
                   let uu___6 = cb g i in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let e =
                   FStarC_Extraction_ML_Syntax.with_ty mlty
                     (FStarC_Extraction_ML_Syntax.MLE_App (bang, [a1; i1])) in
                 (e, FStarC_Extraction_ML_Syntax.E_PURE, mlty)
             | (uu___3, uu___4,
                (t1, uu___5)::(a, FStar_Pervasives_Native.None)::(i,
                                                                  FStar_Pervasives_Native.None)::_l::_r::_p::_s::[])
                 when
                 let uu___6 =
                   FStarC_Ident.lid_of_str
                     "Pulse.Lib.Array.Core.pts_to_range_index" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let mlty = FStarC_Extraction_ML_Term.term_as_mlty g t1 in
                 let bang =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.ml_unit_ty
                     (FStarC_Extraction_ML_Syntax.MLE_Var "Array.get") in
                 let a1 =
                   let uu___6 = cb g a in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let i1 =
                   let uu___6 = cb g i in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let e =
                   FStarC_Extraction_ML_Syntax.with_ty mlty
                     (FStarC_Extraction_ML_Syntax.MLE_App (bang, [a1; i1])) in
                 (e, FStarC_Extraction_ML_Syntax.E_PURE, mlty)
             | (uu___3, uu___4,
                (t1, uu___5)::(a, FStar_Pervasives_Native.None)::(i,
                                                                  FStar_Pervasives_Native.None)::
                (v, FStar_Pervasives_Native.None)::_s::[]) when
                 let uu___6 =
                   FStarC_Ident.lid_of_str
                     "Pulse.Lib.Array.Core.op_Array_Assignment" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let mlty = FStarC_Extraction_ML_Term.term_as_mlty g t1 in
                 let bang =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.ml_unit_ty
                     (FStarC_Extraction_ML_Syntax.MLE_Var "Array.set") in
                 let a1 =
                   let uu___6 = cb g a in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let i1 =
                   let uu___6 = cb g i in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let v1 =
                   let uu___6 = cb g v in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let e =
                   FStarC_Extraction_ML_Syntax.with_ty mlty
                     (FStarC_Extraction_ML_Syntax.MLE_App
                        (bang, [a1; i1; v1])) in
                 (e, FStarC_Extraction_ML_Syntax.E_PURE, mlty)
             | (uu___3, uu___4,
                (t1, uu___5)::(a, FStar_Pervasives_Native.None)::(i,
                                                                  FStar_Pervasives_Native.None)::
                (v, FStar_Pervasives_Native.None)::_l::_r::_s::[]) when
                 let uu___6 =
                   FStarC_Ident.lid_of_str
                     "Pulse.Lib.Array.Core.pts_to_range_upd" in
                 FStarC_Syntax_Syntax.fv_eq_lid fv uu___6 ->
                 let mlty = FStarC_Extraction_ML_Term.term_as_mlty g t1 in
                 let bang =
                   FStarC_Extraction_ML_Syntax.with_ty
                     FStarC_Extraction_ML_Syntax.ml_unit_ty
                     (FStarC_Extraction_ML_Syntax.MLE_Var "Array.set") in
                 let a1 =
                   let uu___6 = cb g a in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let i1 =
                   let uu___6 = cb g i in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let v1 =
                   let uu___6 = cb g v in
                   FStar_Pervasives_Native.__proj__Mktuple3__item___1 uu___6 in
                 let e =
                   FStarC_Extraction_ML_Syntax.with_ty mlty
                     (FStarC_Extraction_ML_Syntax.MLE_App
                        (bang, [a1; i1; v1])) in
                 (e, FStarC_Extraction_ML_Syntax.E_PURE, mlty)
             | uu___3 ->
                 FStarC_Compiler_Effect.raise
                   FStarC_Extraction_ML_Term.NotSupportedByExtension)))
let (uu___0 : unit) =
  FStarC_Extraction_ML_Term.register_pre_translate_typ tr_typ
let (uu___1 : unit) =
  FStarC_Extraction_ML_Term.register_pre_translate tr_expr