open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu___ ->
    let uu___1 = FStar_Options.codegen () in
    uu___1 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
let pruneNones :
  'a . 'a FStar_Pervasives_Native.option Prims.list -> 'a Prims.list =
  fun l ->
    FStar_Compiler_List.fold_right
      (fun x ->
         fun ll ->
           match x with
           | FStar_Pervasives_Native.Some xs -> xs :: ll
           | FStar_Pervasives_Native.None -> ll) l []
let (mk_range_mle : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top
    (FStar_Extraction_ML_Syntax.MLE_Name (["FStar"; "Range"], "mk_range"))
let (dummy_range_mle : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top
    (FStar_Extraction_ML_Syntax.MLE_Name (["FStar"; "Range"], "dummyRange"))
let (mlconst_of_const' :
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant) =
  fun sctt ->
    match sctt with
    | FStar_Const.Const_effect ->
        FStar_Compiler_Effect.failwith "Unsupported constant"
    | FStar_Const.Const_range uu___ -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s, i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_string (s, uu___) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of ->
        FStar_Compiler_Effect.failwith
          "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of ->
        FStar_Compiler_Effect.failwith
          "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu___ ->
        FStar_Compiler_Effect.failwith
          "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify uu___ ->
        FStar_Compiler_Effect.failwith
          "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu___ ->
        FStar_Compiler_Effect.failwith
          "Unhandled constant: real/reify/reflect"
let (mlconst_of_const :
  FStar_Compiler_Range_Type.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p ->
    fun c ->
      try (fun uu___ -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Compiler_Range_Ops.string_of_range p in
            let uu___3 = FStar_Syntax_Print.const_to_string c in
            FStar_Compiler_Util.format2
              "(%s) Failed to translate constant %s " uu___2 uu___3 in
          FStar_Compiler_Effect.failwith uu___1
let (mlexpr_of_range :
  FStar_Compiler_Range_Type.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r ->
    let cint i =
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Compiler_Util.string_of_int i in
            (uu___3, FStar_Pervasives_Native.None) in
          FStar_Extraction_ML_Syntax.MLC_Int uu___2 in
        FStar_Extraction_ML_Syntax.MLE_Const uu___1 in
      FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.ml_int_ty
        uu___ in
    let cstr s =
      FStar_Extraction_ML_Syntax.with_ty
        FStar_Extraction_ML_Syntax.ml_string_ty
        (FStar_Extraction_ML_Syntax.MLE_Const
           (FStar_Extraction_ML_Syntax.MLC_String s)) in
    let drop_path = FStar_Compiler_Util.basename in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Compiler_Range_Ops.file_of_range r in
            drop_path uu___4 in
          cstr uu___3 in
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = FStar_Compiler_Range_Ops.start_of_range r in
              FStar_Compiler_Range_Ops.line_of_pos uu___6 in
            cint uu___5 in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStar_Compiler_Range_Ops.start_of_range r in
                FStar_Compiler_Range_Ops.col_of_pos uu___8 in
              cint uu___7 in
            let uu___7 =
              let uu___8 =
                let uu___9 =
                  let uu___10 = FStar_Compiler_Range_Ops.end_of_range r in
                  FStar_Compiler_Range_Ops.line_of_pos uu___10 in
                cint uu___9 in
              let uu___9 =
                let uu___10 =
                  let uu___11 =
                    let uu___12 = FStar_Compiler_Range_Ops.end_of_range r in
                    FStar_Compiler_Range_Ops.col_of_pos uu___12 in
                  cint uu___11 in
                [uu___10] in
              uu___8 :: uu___9 in
            uu___6 :: uu___7 in
          uu___4 :: uu___5 in
        uu___2 :: uu___3 in
      (mk_range_mle, uu___1) in
    FStar_Extraction_ML_Syntax.MLE_App uu___
let (mlexpr_of_const :
  FStar_Compiler_Range_Type.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p ->
    fun c ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu___ ->
          let uu___1 = mlconst_of_const p c in
          FStar_Extraction_ML_Syntax.MLE_Const uu___1
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu___ =
            FStar_Compiler_Util.find_opt
              (fun uu___1 -> match uu___1 with | (y, uu___2) -> y = x) subst in
          (match uu___ with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
          let uu___ =
            let uu___1 = subst_aux subst t1 in
            let uu___2 = subst_aux subst t2 in (uu___1, f, uu___2) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu___
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, path) ->
          let uu___ =
            let uu___1 = FStar_Compiler_List.map (subst_aux subst) args in
            (uu___1, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu___
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu___ = FStar_Compiler_List.map (subst_aux subst) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu___
      | FStar_Extraction_ML_Syntax.MLTY_Top -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased -> t
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    fun args ->
      match uu___ with
      | (formals, t) ->
          if
            (FStar_Compiler_List.length formals) <>
              (FStar_Compiler_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu___2 =
               let uu___3 =
                 let uu___4 =
                   FStar_Extraction_ML_Syntax.ty_param_names formals in
                 FStar_Compiler_List.zip uu___4 args in
               subst_aux uu___3 t in
             FStar_Pervasives_Native.Some uu___2)
let (subst :
  (FStar_Extraction_ML_Syntax.ty_param Prims.list *
    FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts ->
    fun args ->
      let uu___ = try_subst ts args in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStar_Compiler_Effect.failwith
            "Substitution must be fully applied (see GitHub issue #490)"
      | FStar_Pervasives_Native.Some t -> t
let (udelta_unfold :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun g ->
    fun uu___ ->
      match uu___ with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, n) ->
          let uu___1 = FStar_Extraction_ML_UEnv.lookup_tydef g n in
          (match uu___1 with
           | FStar_Pervasives_Native.Some ts ->
               let uu___2 = try_subst ts args in
               (match uu___2 with
                | FStar_Pervasives_Native.None ->
                    let uu___3 =
                      let uu___4 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n in
                      let uu___5 =
                        FStar_Compiler_Util.string_of_int
                          (FStar_Compiler_List.length args) in
                      let uu___6 =
                        FStar_Compiler_Util.string_of_int
                          (FStar_Compiler_List.length
                             (FStar_Pervasives_Native.fst ts)) in
                      FStar_Compiler_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu___4 uu___5 uu___6 in
                    FStar_Compiler_Effect.failwith uu___3
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu___2 -> FStar_Pervasives_Native.None)
      | uu___1 -> FStar_Pervasives_Native.None
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f ->
    fun f' ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE, uu___) -> true
      | (FStar_Extraction_ML_Syntax.E_ERASABLE,
         FStar_Extraction_ML_Syntax.E_ERASABLE) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE,
         FStar_Extraction_ML_Syntax.E_IMPURE) -> true
      | uu___ -> false
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Extraction_ML_Syntax.E_PURE -> "Pure"
    | FStar_Extraction_ML_Syntax.E_ERASABLE -> "Erasable"
    | FStar_Extraction_ML_Syntax.E_IMPURE -> "Impure"
let (join :
  FStar_Compiler_Range_Type.range ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.e_tag -> FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r ->
    fun f ->
      fun f' ->
        match (f, f') with
        | (FStar_Extraction_ML_Syntax.E_IMPURE,
           FStar_Extraction_ML_Syntax.E_PURE) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_PURE,
           FStar_Extraction_ML_Syntax.E_IMPURE) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_IMPURE,
           FStar_Extraction_ML_Syntax.E_IMPURE) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_ERASABLE,
           FStar_Extraction_ML_Syntax.E_ERASABLE) ->
            FStar_Extraction_ML_Syntax.E_ERASABLE
        | (FStar_Extraction_ML_Syntax.E_PURE,
           FStar_Extraction_ML_Syntax.E_ERASABLE) ->
            FStar_Extraction_ML_Syntax.E_ERASABLE
        | (FStar_Extraction_ML_Syntax.E_ERASABLE,
           FStar_Extraction_ML_Syntax.E_PURE) ->
            FStar_Extraction_ML_Syntax.E_ERASABLE
        | (FStar_Extraction_ML_Syntax.E_PURE,
           FStar_Extraction_ML_Syntax.E_PURE) ->
            FStar_Extraction_ML_Syntax.E_PURE
        | uu___ ->
            let uu___1 =
              let uu___2 = FStar_Compiler_Range_Ops.string_of_range r in
              let uu___3 = eff_to_string f in
              let uu___4 = eff_to_string f' in
              FStar_Compiler_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu___2
                uu___3 uu___4 in
            FStar_Compiler_Effect.failwith uu___1
let (join_l :
  FStar_Compiler_Range_Type.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r ->
    fun fs ->
      FStar_Compiler_List.fold_left (join r)
        FStar_Extraction_ML_Syntax.E_PURE fs
let (mk_ty_fun :
  FStar_Extraction_ML_Syntax.mlbinder Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  FStar_Compiler_List.fold_right
    (fun uu___ ->
       fun t ->
         match uu___ with
         | { FStar_Extraction_ML_Syntax.mlbinder_name = uu___1;
             FStar_Extraction_ML_Syntax.mlbinder_ty = mlbinder_ty;
             FStar_Extraction_ML_Syntax.mlbinder_attrs = uu___2;_} ->
             FStar_Extraction_ML_Syntax.MLTY_Fun
               (mlbinder_ty, FStar_Extraction_ML_Syntax.E_PURE, t))
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
let rec (type_leq_c :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr
            FStar_Pervasives_Native.option))
  =
  fun unfold_ty ->
    fun e ->
      fun t ->
        fun t' ->
          match (t, t') with
          | (FStar_Extraction_ML_Syntax.MLTY_Var x,
             FStar_Extraction_ML_Syntax.MLTY_Var y) ->
              if x = y
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2),
             FStar_Extraction_ML_Syntax.MLTY_Fun (t1', f', t2')) ->
              let mk_fun xs body =
                match xs with
                | [] -> body
                | uu___ ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys, body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_Compiler_List.op_At xs ys), body1)
                      | uu___1 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu___1 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu___1 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs, body);
                     FStar_Extraction_ML_Syntax.mlty = uu___;
                     FStar_Extraction_ML_Syntax.loc = uu___1;_}
                   ->
                   let uu___2 = (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu___2
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_ERASABLE)
                      then
                        let uu___3 = type_leq unfold_ty t2 t2' in
                        (if uu___3
                         then
                           let body1 =
                             let uu___4 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu___4
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_Extraction_ML_Syntax.with_ty t2'
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 mk_ty_fun [x]
                                   body1.FStar_Extraction_ML_Syntax.mlty in
                               FStar_Extraction_ML_Syntax.with_ty uu___6
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu___5 in
                           (true, uu___4)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu___4 =
                           let uu___5 =
                             let uu___6 = mk_fun xs body in
                             FStar_Pervasives_Native.Some uu___6 in
                           type_leq_c unfold_ty uu___5 t2 t2' in
                         match uu___4 with
                         | (ok, body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu___5 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu___5
                               | uu___5 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu___ ->
                   let uu___1 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu___1
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named (args, path),
             FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) ->
              if path = path'
              then
                let uu___ =
                  FStar_Compiler_List.forall2 (type_leq unfold_ty) args args' in
                (if uu___
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu___1 = unfold_ty t in
                 match uu___1 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None ->
                     let uu___2 = unfold_ty t' in
                     (match uu___2 with
                      | FStar_Pervasives_Native.None ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple ts,
             FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu___ =
                FStar_Compiler_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu___
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top,
             FStar_Extraction_ML_Syntax.MLTY_Top) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu___, uu___1) ->
              let uu___2 = unfold_ty t in
              (match uu___2 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu___3 -> (false, FStar_Pervasives_Native.None))
          | (uu___, FStar_Extraction_ML_Syntax.MLTY_Named uu___1) ->
              let uu___2 = unfold_ty t' in
              (match uu___2 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu___3 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased,
             FStar_Extraction_ML_Syntax.MLTY_Erased) -> (true, e)
          | uu___ -> (false, FStar_Pervasives_Native.None)
and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        let uu___ = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_Pervasives_Native.fst uu___
let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
        let uu___ =
          let uu___1 = erase_effect_annotations t1 in
          let uu___2 = erase_effect_annotations t2 in
          (uu___1, FStar_Extraction_ML_Syntax.E_PURE, uu___2) in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu___
    | uu___ -> t
let is_type_abstraction :
  'a 'b 'c . (('a, 'b) FStar_Pervasives.either * 'c) Prims.list -> Prims.bool
  =
  fun uu___ ->
    match uu___ with
    | (FStar_Pervasives.Inl uu___1, uu___2)::uu___3 -> true
    | uu___1 -> false
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | (ns, n) ->
        let uu___1 =
          let uu___2 =
            FStar_Compiler_Util.concat_l "."
              (FStar_Compiler_List.op_At ns [n]) in
          FStar_Parser_Const.is_tuple_datacon_string uu___2 in
        if uu___1
        then
          let uu___2 =
            let uu___3 = FStar_Compiler_Util.char_at n (Prims.of_int (7)) in
            FStar_Compiler_Util.int_of_char uu___3 in
          FStar_Pervasives_Native.Some uu___2
        else FStar_Pervasives_Native.None
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) ->
        let uu___ = is_xtuple mlp in
        (match uu___ with
         | FStar_Pervasives_Native.Some n ->
             FStar_Extraction_ML_Syntax.with_ty
               e.FStar_Extraction_ML_Syntax.mlty
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu___1 -> e)
    | uu___ -> e
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___ ->
    match uu___ with
    | f::uu___1 ->
        let uu___2 =
          let uu___3 = FStar_Ident.ns_of_lid f in
          FStar_Compiler_Util.prefix uu___3 in
        (match uu___2 with
         | (ns, uu___3) ->
             FStar_Compiler_List.map (fun id -> FStar_Ident.string_of_id id)
               ns)
    | uu___1 -> FStar_Compiler_Effect.failwith "impos"
let record_fields :
  'a .
    FStar_Ident.lident Prims.list ->
      'a Prims.list -> (Prims.string * 'a) Prims.list
  =
  fun fs ->
    fun vs ->
      FStar_Compiler_List.map2
        (fun f ->
           fun e ->
             let uu___ =
               let uu___1 = FStar_Ident.ident_of_lid f in
               FStar_Ident.string_of_id uu___1 in
             (uu___, e)) fs vs
let (is_xtuple_ty :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | (ns, n) ->
        let uu___1 =
          let uu___2 =
            FStar_Compiler_Util.concat_l "."
              (FStar_Compiler_List.op_At ns [n]) in
          FStar_Parser_Const.is_tuple_constructor_string uu___2 in
        if uu___1
        then
          let uu___2 =
            let uu___3 = FStar_Compiler_Util.char_at n (Prims.of_int (5)) in
            FStar_Compiler_Util.int_of_char uu___3 in
          FStar_Pervasives_Native.Some uu___2
        else FStar_Pervasives_Native.None
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) ->
        let uu___ = is_xtuple_ty mlp in
        (match uu___ with
         | FStar_Pervasives_Native.Some n ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu___1 -> t)
    | uu___ -> t
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns -> FStar_Compiler_String.concat "_" ns
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | (ns, n) ->
        FStar_Compiler_String.concat "_" (FStar_Compiler_List.op_At ns [n])
let (ml_module_name_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let mlp =
      let uu___ =
        let uu___1 = FStar_Ident.ns_of_lid l in
        FStar_Compiler_List.map FStar_Ident.string_of_id uu___1 in
      let uu___1 =
        let uu___2 = FStar_Ident.ident_of_lid l in
        FStar_Ident.string_of_id uu___2 in
      (uu___, uu___1) in
    flatten_mlpath mlp
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty ->
    fun t ->
      let erasableTypeNoDelta t1 =
        if t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
        then true
        else
          (match t1 with
           | FStar_Extraction_ML_Syntax.MLTY_Named
               (uu___1, ("FStar"::"Ghost"::[], "erased")) -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named
               (uu___1, ("FStar"::"Tactics"::"Effect"::[], "tactic")) ->
               let uu___2 = FStar_Options.codegen () in
               uu___2 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
           | uu___1 -> false) in
      let uu___ = erasableTypeNoDelta t in
      if uu___
      then true
      else
        (let uu___2 = unfold_ty t in
         match uu___2 with
         | FStar_Pervasives_Native.Some t1 -> erasableType unfold_ty t1
         | FStar_Pervasives_Native.None -> false)
let rec (eraseTypeDeep :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun unfold_ty ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Fun (tyd, etag, tycd) ->
          if etag = FStar_Extraction_ML_Syntax.E_PURE
          then
            let uu___ =
              let uu___1 = eraseTypeDeep unfold_ty tyd in
              let uu___2 = eraseTypeDeep unfold_ty tycd in
              (uu___1, etag, uu___2) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu___
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) ->
          let uu___ = erasableType unfold_ty t in
          if uu___
          then FStar_Extraction_ML_Syntax.MLTY_Erased
          else
            (let uu___2 =
               let uu___3 =
                 FStar_Compiler_List.map (eraseTypeDeep unfold_ty) lty in
               (uu___3, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu___2)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu___ = FStar_Compiler_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu___
      | uu___ -> t
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu___ =
    mk_ty_fun
      [{
         FStar_Extraction_ML_Syntax.mlbinder_name = "x";
         FStar_Extraction_ML_Syntax.mlbinder_ty =
           FStar_Extraction_ML_Syntax.ml_bool_ty;
         FStar_Extraction_ML_Syntax.mlbinder_attrs = []
       };
      {
        FStar_Extraction_ML_Syntax.mlbinder_name = "y";
        FStar_Extraction_ML_Syntax.mlbinder_ty =
          FStar_Extraction_ML_Syntax.ml_bool_ty;
        FStar_Extraction_ML_Syntax.mlbinder_attrs = []
      }] FStar_Extraction_ML_Syntax.ml_bool_ty in
  FStar_Extraction_ML_Syntax.with_ty uu___
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_AmpAmp"))
let (conjoin :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun e1 ->
    fun e2 ->
      FStar_Extraction_ML_Syntax.with_ty
        FStar_Extraction_ML_Syntax.ml_bool_ty
        (FStar_Extraction_ML_Syntax.MLE_App (prims_op_amp_amp, [e1; e2]))
let (conjoin_opt :
  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option)
  =
  fun e1 ->
    fun e2 ->
      match (e1, e2) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          FStar_Pervasives_Native.None
      | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.None) ->
          FStar_Pervasives_Native.Some x
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some x) ->
          FStar_Pervasives_Native.Some x
      | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
          let uu___ = conjoin x y in FStar_Pervasives_Native.Some uu___
let (mlloc_of_range :
  FStar_Compiler_Range_Type.range -> (Prims.int * Prims.string)) =
  fun r ->
    let pos = FStar_Compiler_Range_Ops.start_of_range r in
    let line = FStar_Compiler_Range_Ops.line_of_pos pos in
    let uu___ = FStar_Compiler_Range_Ops.file_of_range r in (line, uu___)
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu___, b) ->
        let uu___1 = doms_and_cod b in
        (match uu___1 with | (ds, c) -> ((a :: ds), c))
    | uu___ -> ([], t)
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  = fun t -> let uu___ = doms_and_cod t in FStar_Pervasives_Native.fst uu___
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu___, b) ->
        let uu___1 = uncurry_mlty_fun b in
        (match uu___1 with | (args, res) -> ((a :: args), res))
    | uu___ -> ([], t)
let (list_elements :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.list
      FStar_Pervasives_Native.option)
  =
  fun e ->
    let rec list_elements1 acc e1 =
      match e1.FStar_Extraction_ML_Syntax.expr with
      | FStar_Extraction_ML_Syntax.MLE_CTor
          (("Prims"::[], "Cons"), hd::tl::[]) ->
          list_elements1 (hd :: acc) tl
      | FStar_Extraction_ML_Syntax.MLE_CTor (("Prims"::[], "Nil"), []) ->
          FStar_Pervasives_Native.Some (FStar_Compiler_List.rev acc)
      | uu___ -> FStar_Pervasives_Native.None in
    list_elements1 [] e