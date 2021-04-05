open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu___ ->
    let uu___1 = FStar_Options.codegen () in
    uu___1 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
let pruneNones :
  'a . 'a FStar_Pervasives_Native.option Prims.list -> 'a Prims.list =
  fun l ->
    FStar_List.fold_right
      (fun x ->
         fun ll ->
           match x with
           | FStar_Pervasives_Native.Some xs -> xs :: ll
           | FStar_Pervasives_Native.None -> ll) l []
let (mk_range_mle : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "mk_range"))
let (dummy_range_mle : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["FStar"; "Range"], "dummyRange"))
let (fstar_real_of_string : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["FStar"; "Real"], "of_string"))
let (mlconst_of_const' :
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant) =
  fun sctt ->
    match sctt with
    | FStar_Const.Const_effect -> failwith "Unsupported constant"
    | FStar_Const.Const_range uu___ -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s, i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes, uu___) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s, uu___) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu___ ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu___ ->
        failwith "Unhandled constant: real/reify/reflect"
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p ->
    fun c ->
      try (fun uu___ -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___ ->
          let uu___1 =
            let uu___2 = FStar_Range.string_of_range p in
            let uu___3 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s " uu___2
              uu___3 in
          failwith uu___1
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r ->
    let cint i =
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Util.string_of_int i in
            (uu___3, FStar_Pervasives_Native.None) in
          FStar_Extraction_ML_Syntax.MLC_Int uu___2 in
        FStar_All.pipe_right uu___1
          (fun uu___2 -> FStar_Extraction_ML_Syntax.MLE_Const uu___2) in
      FStar_All.pipe_right uu___
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty) in
    let cstr s =
      let uu___ =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun uu___1 -> FStar_Extraction_ML_Syntax.MLE_Const uu___1) in
      FStar_All.pipe_right uu___
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty) in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Range.file_of_range r in
          FStar_All.pipe_right uu___3 cstr in
        let uu___3 =
          let uu___4 =
            let uu___5 =
              let uu___6 = FStar_Range.start_of_range r in
              FStar_All.pipe_right uu___6 FStar_Range.line_of_pos in
            FStar_All.pipe_right uu___5 cint in
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStar_Range.start_of_range r in
                FStar_All.pipe_right uu___8 FStar_Range.col_of_pos in
              FStar_All.pipe_right uu___7 cint in
            let uu___7 =
              let uu___8 =
                let uu___9 =
                  let uu___10 = FStar_Range.end_of_range r in
                  FStar_All.pipe_right uu___10 FStar_Range.line_of_pos in
                FStar_All.pipe_right uu___9 cint in
              let uu___9 =
                let uu___10 =
                  let uu___11 =
                    let uu___12 = FStar_Range.end_of_range r in
                    FStar_All.pipe_right uu___12 FStar_Range.col_of_pos in
                  FStar_All.pipe_right uu___11 cint in
                [uu___10] in
              uu___8 :: uu___9 in
            uu___6 :: uu___7 in
          uu___4 :: uu___5 in
        uu___2 :: uu___3 in
      (mk_range_mle, uu___1) in
    FStar_Extraction_ML_Syntax.MLE_App uu___
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p ->
    fun c ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | FStar_Const.Const_real s ->
          let str = mlconst_of_const p (FStar_Const.Const_string (s, p)) in
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_All.pipe_left
                  (FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.ml_string_ty)
                  (FStar_Extraction_ML_Syntax.MLE_Const str) in
              [uu___2] in
            (fstar_real_of_string, uu___1) in
          FStar_Extraction_ML_Syntax.MLE_App uu___
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
            FStar_Util.find_opt
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
            let uu___1 = FStar_List.map (subst_aux subst) args in
            (uu___1, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu___
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu___ = FStar_List.map (subst_aux subst) ts in
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
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu___2 =
               let uu___3 = FStar_List.zip formals args in subst_aux uu___3 t in
             FStar_Pervasives_Native.Some uu___2)
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts ->
    fun args ->
      let uu___ = try_subst ts args in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          failwith
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
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu___6 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu___4 uu___5 uu___6 in
                    failwith uu___3
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
      | (FStar_Extraction_ML_Syntax.E_GHOST,
         FStar_Extraction_ML_Syntax.E_GHOST) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE,
         FStar_Extraction_ML_Syntax.E_IMPURE) -> true
      | uu___ -> false
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_Extraction_ML_Syntax.E_PURE -> "Pure"
    | FStar_Extraction_ML_Syntax.E_GHOST -> "Ghost"
    | FStar_Extraction_ML_Syntax.E_IMPURE -> "Impure"
let (join :
  FStar_Range.range ->
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
        | (FStar_Extraction_ML_Syntax.E_GHOST,
           FStar_Extraction_ML_Syntax.E_GHOST) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_PURE,
           FStar_Extraction_ML_Syntax.E_GHOST) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_GHOST,
           FStar_Extraction_ML_Syntax.E_PURE) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_PURE,
           FStar_Extraction_ML_Syntax.E_PURE) ->
            FStar_Extraction_ML_Syntax.E_PURE
        | uu___ ->
            let uu___1 =
              let uu___2 = FStar_Range.string_of_range r in
              let uu___3 = eff_to_string f in
              let uu___4 = eff_to_string f' in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu___2
                uu___3 uu___4 in
            failwith uu___1
let (join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r ->
    fun fs ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let (mk_ty_fun :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  FStar_List.fold_right
    (fun uu___ ->
       fun t ->
         match uu___ with
         | (uu___1, t0) ->
             FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
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
                            ((FStar_List.append xs ys), body1)
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
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
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
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu___4 =
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu___7 in
                               FStar_All.pipe_left uu___6
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu___5 in
                           (true, uu___4)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu___4 =
                           let uu___5 =
                             let uu___6 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun uu___7 ->
                                  FStar_Pervasives_Native.Some uu___7) uu___6 in
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
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
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
              let uu___ = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
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
        FStar_All.pipe_right uu___ FStar_Pervasives_Native.fst
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
          let uu___2 = FStar_Util.concat_l "." (FStar_List.append ns [n]) in
          FStar_Parser_Const.is_tuple_datacon_string uu___2 in
        if uu___1
        then
          let uu___2 =
            let uu___3 = FStar_Util.char_at n (Prims.of_int (7)) in
            FStar_Util.int_of_char uu___3 in
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
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu___1 -> e)
    | uu___ -> e
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___ ->
    match uu___ with
    | f::uu___1 ->
        let uu___2 =
          let uu___3 = FStar_Ident.ns_of_lid f in FStar_Util.prefix uu___3 in
        (match uu___2 with
         | (ns, uu___3) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id -> FStar_Ident.string_of_id id)))
    | uu___1 -> failwith "impos"
let record_fields :
  'a .
    FStar_Ident.lident Prims.list ->
      'a Prims.list -> (Prims.string * 'a) Prims.list
  =
  fun fs ->
    fun vs ->
      FStar_List.map2
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
          let uu___2 = FStar_Util.concat_l "." (FStar_List.append ns [n]) in
          FStar_Parser_Const.is_tuple_constructor_string uu___2 in
        if uu___1
        then
          let uu___2 =
            let uu___3 = FStar_Util.char_at n (Prims.of_int (5)) in
            FStar_Util.int_of_char uu___3 in
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
  fun ns -> FStar_String.concat "_" ns
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | (ns, n) -> FStar_String.concat "_" (FStar_List.append ns [n])
let (ml_module_name_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let mlp =
      let uu___ =
        let uu___1 = FStar_All.pipe_right l FStar_Ident.ns_of_lid in
        FStar_All.pipe_right uu___1 (FStar_List.map FStar_Ident.string_of_id) in
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
               let uu___3 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu___3, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu___2)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu___ = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu___
      | uu___ -> t
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu___ =
    let uu___1 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu___1 in
  FStar_All.pipe_left uu___
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_AmpAmp"))
let (conjoin :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun e1 ->
    fun e2 ->
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_bool_ty)
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
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu___ = FStar_Range.file_of_range r in (line, uu___)
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
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | NoTacticEmbedding uu___ -> true | uu___ -> false
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | NoTacticEmbedding uu___ -> uu___
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r ->
    fun t ->
      fun msg ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStar_Errors.lookup
                    FStar_Errors.Warning_PluginNotImplemented in
                FStar_Errors.error_number uu___4 in
              FStar_All.pipe_left FStar_Util.string_of_int uu___3 in
            FStar_Util.format3
              "Plugin %s can not run natively because %s (use --warn_error -%s to carry on)."
              t msg uu___2 in
          (FStar_Errors.Warning_PluginNotImplemented, uu___1) in
        FStar_Errors.log_issue r uu___
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee ->
    match projectee with | Syntax_term -> true | uu___ -> false
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee -> match projectee with | Refl_emb -> true | uu___ -> false
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee -> match projectee with | NBE_t -> true | uu___ -> false
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee ->
    match projectee with | NBERefl_emb -> true | uu___ -> false
type wrapped_term =
  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlexpr *
    Prims.int * Prims.bool)
let (interpret_plugin_as_term_fun :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ ->
        Prims.int FStar_Pervasives_Native.option ->
          FStar_Extraction_ML_Syntax.mlexpr' ->
            (FStar_Extraction_ML_Syntax.mlexpr *
              FStar_Extraction_ML_Syntax.mlexpr * Prims.int * Prims.bool)
              FStar_Pervasives_Native.option)
  =
  fun env ->
    fun fv ->
      fun t ->
        fun arity_opt ->
          fun ml_fv ->
            let fv_lid =
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let tcenv = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            let t1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.EraseUniverses;
                FStar_TypeChecker_Env.AllowUnboundUniverses;
                FStar_TypeChecker_Env.UnfoldUntil
                  FStar_Syntax_Syntax.delta_constant;
                FStar_TypeChecker_Env.ForExtraction] tcenv t in
            let w =
              FStar_Extraction_ML_Syntax.with_ty
                FStar_Extraction_ML_Syntax.MLTY_Top in
            let as_name mlp =
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top)
                (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
            let lid_to_name l =
              let uu___ =
                let uu___1 = FStar_Extraction_ML_UEnv.mlpath_of_lident env l in
                FStar_Extraction_ML_Syntax.MLE_Name uu___1 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu___ in
            let str_to_name s = as_name ([], s) in
            let fstar_tc_nbe_prefix s =
              as_name (["FStar_TypeChecker_NBETerm"], s) in
            let fstar_syn_emb_prefix s =
              as_name (["FStar_Syntax_Embeddings"], s) in
            let fstar_refl_emb_prefix s =
              as_name (["FStar_Reflection_Embeddings"], s) in
            let fstar_refl_nbeemb_prefix s =
              as_name (["FStar_Reflection_NBEEmbeddings"], s) in
            let fv_lid_embedded =
              let uu___ =
                let uu___1 =
                  let uu___2 = as_name (["FStar_Ident"], "lid_of_str") in
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = FStar_Ident.string_of_lid fv_lid in
                          FStar_Extraction_ML_Syntax.MLC_String uu___7 in
                        FStar_Extraction_ML_Syntax.MLE_Const uu___6 in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu___5 in
                    [uu___4] in
                  (uu___2, uu___3) in
                FStar_Extraction_ML_Syntax.MLE_App uu___1 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu___ in
            let emb_prefix uu___ =
              match uu___ with
              | Syntax_term -> fstar_syn_emb_prefix
              | Refl_emb -> fstar_refl_emb_prefix
              | NBE_t -> fstar_tc_nbe_prefix
              | NBERefl_emb -> fstar_refl_nbeemb_prefix in
            let mk_tactic_interpretation l arity =
              if arity > FStar_Tactics_InterpFuns.max_tac_arity
              then
                FStar_Exn.raise
                  (NoTacticEmbedding
                     "tactic plugins can only take up to 20 arguments")
              else
                (let idroot =
                   match l with
                   | Syntax_term -> "mk_tactic_interpretation_"
                   | uu___1 -> "mk_nbe_tactic_interpretation_" in
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStar_Util.string_of_int arity in
                     Prims.op_Hat idroot uu___3 in
                   (["FStar_Tactics_InterpFuns"], uu___2) in
                 as_name uu___1) in
            let mk_from_tactic l arity =
              let idroot =
                match l with
                | Syntax_term -> "from_tactic_"
                | uu___ -> "from_nbe_tactic_" in
              let uu___ =
                let uu___1 =
                  let uu___2 = FStar_Util.string_of_int arity in
                  Prims.op_Hat idroot uu___2 in
                (["FStar_Tactics_Native"], uu___1) in
              as_name uu___ in
            let mk_basic_embedding l s =
              if s = "norm_step"
              then
                match l with
                | Syntax_term ->
                    as_name (["FStar_Tactics_Builtins"], "e_norm_step'")
                | NBE_t ->
                    as_name (["FStar_Tactics_Builtins"], "e_norm_step_nbe'")
                | uu___ ->
                    failwith "impossible: mk_basic_embedding norm_step"
              else emb_prefix l (Prims.op_Hat "e_" s) in
            let mk_arrow_as_prim_step l arity =
              let uu___ =
                let uu___1 = FStar_Util.string_of_int arity in
                Prims.op_Hat "arrow_as_prim_step_" uu___1 in
              emb_prefix l uu___ in
            let mk_any_embedding l s =
              let uu___ =
                let uu___1 =
                  let uu___2 = emb_prefix l "mk_any_emb" in
                  let uu___3 = let uu___4 = str_to_name s in [uu___4] in
                  (uu___2, uu___3) in
                FStar_Extraction_ML_Syntax.MLE_App uu___1 in
              FStar_All.pipe_left w uu___ in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e)) in
            let emb_arrow l e1 e2 =
              let uu___ =
                let uu___1 =
                  let uu___2 = emb_prefix l "e_arrow" in (uu___2, [e1; e2]) in
                FStar_Extraction_ML_Syntax.MLE_App uu___1 in
              FStar_All.pipe_left w uu___ in
            let known_type_constructors =
              let term_cs =
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.of_int (2))
                                      FStar_Range.dummyRange in
                                  (uu___9, (Prims.of_int (2)), "tuple2") in
                                (uu___8, Syntax_term) in
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    let uu___11 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term" in
                                    (uu___11, Prims.int_zero, "term") in
                                  (uu___10, Refl_emb) in
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      let uu___13 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "sigelt" in
                                      (uu___13, Prims.int_zero, "sigelt") in
                                    (uu___12, Refl_emb) in
                                  let uu___12 =
                                    let uu___13 =
                                      let uu___14 =
                                        let uu___15 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "fv" in
                                        (uu___15, Prims.int_zero, "fv") in
                                      (uu___14, Refl_emb) in
                                    let uu___14 =
                                      let uu___15 =
                                        let uu___16 =
                                          let uu___17 =
                                            FStar_Reflection_Data.fstar_refl_types_lid
                                              "binder" in
                                          (uu___17, Prims.int_zero, "binder") in
                                        (uu___16, Refl_emb) in
                                      let uu___16 =
                                        let uu___17 =
                                          let uu___18 =
                                            let uu___19 =
                                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                                "binders" in
                                            (uu___19, Prims.int_zero,
                                              "binders") in
                                          (uu___18, Refl_emb) in
                                        let uu___18 =
                                          let uu___19 =
                                            let uu___20 =
                                              let uu___21 =
                                                FStar_Reflection_Data.fstar_refl_data_lid
                                                  "exp" in
                                              (uu___21, Prims.int_zero,
                                                "exp") in
                                            (uu___20, Refl_emb) in
                                          [uu___19] in
                                        uu___17 :: uu___18 in
                                      uu___15 :: uu___16 in
                                    uu___13 :: uu___14 in
                                  uu___11 :: uu___12 in
                                uu___9 :: uu___10 in
                              uu___7 :: uu___8 in
                            ((FStar_Parser_Const.option_lid, Prims.int_one,
                               "option"), Syntax_term)
                              :: uu___6 in
                          ((FStar_Parser_Const.list_lid, Prims.int_one,
                             "list"), Syntax_term)
                            :: uu___5 in
                        ((FStar_Parser_Const.norm_step_lid, Prims.int_zero,
                           "norm_step"), Syntax_term)
                          :: uu___4 in
                      ((FStar_Parser_Const.string_lid, Prims.int_zero,
                         "string"), Syntax_term)
                        :: uu___3 in
                    ((FStar_Parser_Const.unit_lid, Prims.int_zero, "unit"),
                      Syntax_term) :: uu___2 in
                  ((FStar_Parser_Const.bool_lid, Prims.int_zero, "bool"),
                    Syntax_term) :: uu___1 in
                ((FStar_Parser_Const.int_lid, Prims.int_zero, "int"),
                  Syntax_term) :: uu___ in
              let nbe_cs =
                FStar_List.map
                  (fun uu___ ->
                     match uu___ with
                     | (x, Syntax_term) -> (x, NBE_t)
                     | (x, Refl_emb) -> (x, NBERefl_emb)
                     | uu___1 -> failwith "Impossible") term_cs in
              fun uu___ ->
                match uu___ with
                | Syntax_term -> term_cs
                | Refl_emb -> term_cs
                | uu___1 -> nbe_cs in
            let is_known_type_constructor l fv1 n =
              FStar_Util.for_some
                (fun uu___ ->
                   match uu___ with
                   | ((x, args, uu___1), uu___2) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n = args))
                (known_type_constructors l) in
            let find_env_entry bv uu___ =
              match uu___ with
              | (bv', uu___1) -> FStar_Syntax_Syntax.bv_eq bv bv' in
            let rec mk_embedding l env1 t2 =
              let t3 =
                FStar_TypeChecker_Normalize.unfold_whnf'
                  [FStar_TypeChecker_Env.ForExtraction] tcenv t2 in
              let uu___ =
                let uu___1 = FStar_Syntax_Subst.compress t3 in
                uu___1.FStar_Syntax_Syntax.n in
              match uu___ with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env1 ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        FStar_Util.find_opt (find_env_entry bv) env1 in
                      FStar_Util.must uu___3 in
                    FStar_Pervasives_Native.snd uu___2 in
                  FStar_All.pipe_left (mk_any_embedding l) uu___1
              | FStar_Syntax_Syntax.Tm_refine (x, uu___1) ->
                  mk_embedding l env1 x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4, uu___1, uu___2) ->
                  mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[], c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu___1 = FStar_Syntax_Subst.open_comp [b] c in
                  (match uu___1 with
                   | (bs, c1) ->
                       let t0 =
                         let uu___2 =
                           let uu___3 = FStar_List.hd bs in
                           uu___3.FStar_Syntax_Syntax.binder_bv in
                         uu___2.FStar_Syntax_Syntax.sort in
                       let t11 = FStar_Syntax_Util.comp_result c1 in
                       let uu___2 = mk_embedding l env1 t0 in
                       let uu___3 = mk_embedding l env1 t11 in
                       emb_arrow l uu___2 uu___3)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs, c) ->
                  let tail =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      t3.FStar_Syntax_Syntax.pos in
                  let t4 =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = FStar_Syntax_Syntax.mk_Total tail in
                        ([b], uu___3) in
                      FStar_Syntax_Syntax.Tm_arrow uu___2 in
                    FStar_Syntax_Syntax.mk uu___1 t3.FStar_Syntax_Syntax.pos in
                  mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_fvar uu___1 ->
                  let uu___2 = FStar_Syntax_Util.head_and_args t3 in
                  (match uu___2 with
                   | (head, args) ->
                       let n_args = FStar_List.length args in
                       let uu___3 =
                         let uu___4 = FStar_Syntax_Util.un_uinst head in
                         uu___4.FStar_Syntax_Syntax.n in
                       (match uu___3 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu___4 ->
                                      match uu___4 with
                                      | (t4, uu___5) ->
                                          mk_embedding l env1 t4)) in
                            let nm =
                              let uu___4 =
                                FStar_Ident.ident_of_lid
                                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                              FStar_Ident.string_of_id uu___4 in
                            let uu___4 =
                              let uu___5 =
                                FStar_Util.find_opt
                                  (fun uu___6 ->
                                     match uu___6 with
                                     | ((x, uu___7, uu___8), uu___9) ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l) in
                              FStar_All.pipe_right uu___5 FStar_Util.must in
                            (match uu___4 with
                             | ((uu___5, t_arity, _trepr_head),
                                loc_embedding) ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm in
                                 (match t_arity with
                                  | uu___6 when uu___6 = Prims.int_zero ->
                                      head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu___4 ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Print.term_to_string t3 in
                                Prims.op_Hat
                                  "Embedding not defined for type " uu___7 in
                              NoTacticEmbedding uu___6 in
                            FStar_Exn.raise uu___5))
              | FStar_Syntax_Syntax.Tm_uinst uu___1 ->
                  let uu___2 = FStar_Syntax_Util.head_and_args t3 in
                  (match uu___2 with
                   | (head, args) ->
                       let n_args = FStar_List.length args in
                       let uu___3 =
                         let uu___4 = FStar_Syntax_Util.un_uinst head in
                         uu___4.FStar_Syntax_Syntax.n in
                       (match uu___3 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu___4 ->
                                      match uu___4 with
                                      | (t4, uu___5) ->
                                          mk_embedding l env1 t4)) in
                            let nm =
                              let uu___4 =
                                FStar_Ident.ident_of_lid
                                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                              FStar_Ident.string_of_id uu___4 in
                            let uu___4 =
                              let uu___5 =
                                FStar_Util.find_opt
                                  (fun uu___6 ->
                                     match uu___6 with
                                     | ((x, uu___7, uu___8), uu___9) ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l) in
                              FStar_All.pipe_right uu___5 FStar_Util.must in
                            (match uu___4 with
                             | ((uu___5, t_arity, _trepr_head),
                                loc_embedding) ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm in
                                 (match t_arity with
                                  | uu___6 when uu___6 = Prims.int_zero ->
                                      head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu___4 ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Print.term_to_string t3 in
                                Prims.op_Hat
                                  "Embedding not defined for type " uu___7 in
                              NoTacticEmbedding uu___6 in
                            FStar_Exn.raise uu___5))
              | FStar_Syntax_Syntax.Tm_app uu___1 ->
                  let uu___2 = FStar_Syntax_Util.head_and_args t3 in
                  (match uu___2 with
                   | (head, args) ->
                       let n_args = FStar_List.length args in
                       let uu___3 =
                         let uu___4 = FStar_Syntax_Util.un_uinst head in
                         uu___4.FStar_Syntax_Syntax.n in
                       (match uu___3 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu___4 ->
                                      match uu___4 with
                                      | (t4, uu___5) ->
                                          mk_embedding l env1 t4)) in
                            let nm =
                              let uu___4 =
                                FStar_Ident.ident_of_lid
                                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                              FStar_Ident.string_of_id uu___4 in
                            let uu___4 =
                              let uu___5 =
                                FStar_Util.find_opt
                                  (fun uu___6 ->
                                     match uu___6 with
                                     | ((x, uu___7, uu___8), uu___9) ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l) in
                              FStar_All.pipe_right uu___5 FStar_Util.must in
                            (match uu___4 with
                             | ((uu___5, t_arity, _trepr_head),
                                loc_embedding) ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm in
                                 (match t_arity with
                                  | uu___6 when uu___6 = Prims.int_zero ->
                                      head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu___4 ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Print.term_to_string t3 in
                                Prims.op_Hat
                                  "Embedding not defined for type " uu___7 in
                              NoTacticEmbedding uu___6 in
                            FStar_Exn.raise uu___5))
              | uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = FStar_Syntax_Print.term_to_string t3 in
                      Prims.op_Hat "Embedding not defined for type " uu___4 in
                    NoTacticEmbedding uu___3 in
                  FStar_Exn.raise uu___2 in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          as_name (["FStar_Syntax_Embeddings"], "debug_wrap") in
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 = FStar_Ident.string_of_lid fv_lid in
                                FStar_Extraction_ML_Syntax.MLC_String uu___7 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu___6 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top) uu___5 in
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 = str_to_name "args" in
                                      [uu___11] in
                                    (body, uu___10) in
                                  FStar_Extraction_ML_Syntax.MLE_App uu___9 in
                                FStar_All.pipe_left w uu___8 in
                              mk_lam "_" uu___7 in
                            [uu___6] in
                          uu___4 :: uu___5 in
                        (uu___2, uu___3) in
                      FStar_Extraction_ML_Syntax.MLE_App uu___1 in
                    FStar_All.pipe_left w uu___ in
                  mk_lam "args" body1
              | uu___ ->
                  let args_tail =
                    FStar_Extraction_ML_Syntax.MLP_Var "args_tail" in
                  let mk_cons hd_pat tail_pat =
                    FStar_Extraction_ML_Syntax.MLP_CTor
                      ((["Prims"], "Cons"), [hd_pat; tail_pat]) in
                  let fst_pat v =
                    FStar_Extraction_ML_Syntax.MLP_Tuple
                      [FStar_Extraction_ML_Syntax.MLP_Var v;
                      FStar_Extraction_ML_Syntax.MLP_Wild] in
                  let pattern =
                    FStar_List.fold_right
                      (fun hd_var -> mk_cons (fst_pat hd_var)) tvar_names
                      args_tail in
                  let branch =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 = as_name ([], "args") in [uu___5] in
                          (body, uu___4) in
                        FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                      FStar_All.pipe_left w uu___2 in
                    (pattern, FStar_Pervasives_Native.None, uu___1) in
                  let default_branch =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = str_to_name "failwith" in
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange)) in
                              FStar_All.pipe_left w uu___7 in
                            [uu___6] in
                          (uu___4, uu___5) in
                        FStar_Extraction_ML_Syntax.MLE_App uu___3 in
                      FStar_All.pipe_left w uu___2 in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu___1) in
                  let body1 =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = as_name ([], "args") in
                        (uu___3, [branch; default_branch]) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu___2 in
                    FStar_All.pipe_left w uu___1 in
                  let body2 =
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          as_name (["FStar_Syntax_Embeddings"], "debug_wrap") in
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 = FStar_Ident.string_of_lid fv_lid in
                                FStar_Extraction_ML_Syntax.MLC_String uu___8 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu___7 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top) uu___6 in
                          let uu___6 =
                            let uu___7 = mk_lam "_" body1 in [uu___7] in
                          uu___5 :: uu___6 in
                        (uu___3, uu___4) in
                      FStar_Extraction_ML_Syntax.MLE_App uu___2 in
                    FStar_All.pipe_left w uu___1 in
                  mk_lam "args" body2 in
            let uu___ = FStar_Syntax_Util.arrow_formals_comp t1 in
            match uu___ with
            | (bs, c) ->
                let uu___1 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None -> (bs, c)
                  | FStar_Pervasives_Native.Some n ->
                      let n_bs = FStar_List.length bs in
                      if n = n_bs
                      then (bs, c)
                      else
                        if n < n_bs
                        then
                          (let uu___3 = FStar_Util.first_N n bs in
                           match uu___3 with
                           | (bs1, rest) ->
                               let c1 =
                                 let uu___4 = FStar_Syntax_Util.arrow rest c in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu___4 in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu___4 = FStar_Ident.string_of_lid fv_lid in
                             let uu___5 = FStar_Util.string_of_int n in
                             let uu___6 = FStar_Util.string_of_int n_bs in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu___4 uu___5 uu___6 in
                           FStar_Exn.raise (NoTacticEmbedding msg)) in
                (match uu___1 with
                 | (bs1, c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1 in
                     let arity = FStar_List.length bs1 in
                     let uu___2 =
                       let uu___3 =
                         FStar_Util.prefix_until
                           (fun uu___4 ->
                              match uu___4 with
                              | { FStar_Syntax_Syntax.binder_bv = b;
                                  FStar_Syntax_Syntax.binder_qual = uu___5;
                                  FStar_Syntax_Syntax.binder_attrs = uu___6;_}
                                  ->
                                  let uu___7 =
                                    let uu___8 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort in
                                    uu___8.FStar_Syntax_Syntax.n in
                                  (match uu___7 with
                                   | FStar_Syntax_Syntax.Tm_type uu___8 ->
                                       false
                                   | uu___8 -> true)) bs1 in
                       match uu___3 with
                       | FStar_Pervasives_Native.None -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars, x, rest) ->
                           (tvars, (x :: rest)) in
                     (match uu___2 with
                      | (type_vars, bs2) ->
                          let tvar_arity = FStar_List.length type_vars in
                          let non_tvar_arity = FStar_List.length bs2 in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i ->
                                 fun tv ->
                                   let uu___3 = FStar_Util.string_of_int i in
                                   Prims.op_Hat "tv_" uu___3) type_vars in
                          let tvar_context =
                            FStar_List.map2
                              (fun b ->
                                 fun nm ->
                                   ((b.FStar_Syntax_Syntax.binder_bv), nm))
                              type_vars tvar_names in
                          let rec aux loc accum_embeddings bs3 =
                            match bs3 with
                            | [] ->
                                let arg_unembeddings =
                                  FStar_List.rev accum_embeddings in
                                let res_embedding =
                                  mk_embedding loc tvar_context result_typ in
                                let fv_lid1 =
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                let uu___3 =
                                  FStar_Syntax_Util.is_pure_comp c1 in
                                if uu___3
                                then
                                  let cb = str_to_name "cb" in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity in
                                  let args =
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 = lid_to_name fv_lid1 in
                                        let uu___7 =
                                          let uu___8 =
                                            let uu___9 =
                                              let uu___10 =
                                                let uu___11 =
                                                  let uu___12 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity in
                                                  (uu___12,
                                                    FStar_Pervasives_Native.None) in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu___11 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu___10 in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu___9 in
                                          [uu___8; fv_lid_embedded; cb] in
                                        uu___6 :: uu___7 in
                                      res_embedding :: uu___5 in
                                    FStar_List.append arg_unembeddings uu___4 in
                                  let fun_embedding =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (embed_fun_N, args)) in
                                  let tabs =
                                    abstract_tvars tvar_names fun_embedding in
                                  let cb_tabs = mk_lam "cb" tabs in
                                  let uu___4 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs in
                                  (uu___4, arity, true)
                                else
                                  (let uu___5 =
                                     let uu___6 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1) in
                                     FStar_Ident.lid_equals uu___6
                                       FStar_Parser_Const.effect_TAC_lid in
                                   if uu___5
                                   then
                                     let h =
                                       mk_tactic_interpretation loc
                                         non_tvar_arity in
                                     let tac_fun =
                                       let uu___6 =
                                         let uu___7 =
                                           let uu___8 =
                                             mk_from_tactic loc
                                               non_tvar_arity in
                                           let uu___9 =
                                             let uu___10 =
                                               lid_to_name fv_lid1 in
                                             [uu___10] in
                                           (uu___8, uu___9) in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu___7 in
                                       FStar_All.pipe_left w uu___6 in
                                     let psc = str_to_name "psc" in
                                     let ncb = str_to_name "ncb" in
                                     let all_args = str_to_name "args" in
                                     let args =
                                       FStar_List.append [tac_fun]
                                         (FStar_List.append arg_unembeddings
                                            [res_embedding; psc; ncb]) in
                                     let tabs =
                                       match tvar_names with
                                       | [] ->
                                           let uu___6 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args]))) in
                                           mk_lam "args" uu___6
                                       | uu___6 ->
                                           let uu___7 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args)) in
                                           abstract_tvars tvar_names uu___7 in
                                     let uu___6 =
                                       let uu___7 = mk_lam "ncb" tabs in
                                       mk_lam "psc" uu___7 in
                                     (uu___6, (arity + Prims.int_one), false)
                                   else
                                     (let uu___7 =
                                        let uu___8 =
                                          let uu___9 =
                                            FStar_Syntax_Print.term_to_string
                                              t1 in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu___9 in
                                        NoTacticEmbedding uu___8 in
                                      FStar_Exn.raise uu___7))
                            | { FStar_Syntax_Syntax.binder_bv = b;
                                FStar_Syntax_Syntax.binder_qual = uu___3;
                                FStar_Syntax_Syntax.binder_attrs = uu___4;_}::bs4
                                ->
                                let uu___5 =
                                  let uu___6 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort in
                                  uu___6 :: accum_embeddings in
                                aux loc uu___5 bs4 in
                          (try
                             (fun uu___3 ->
                                match () with
                                | () ->
                                    let uu___4 = aux Syntax_term [] bs2 in
                                    (match uu___4 with
                                     | (w1, a, b) ->
                                         let uu___5 = aux NBE_t [] bs2 in
                                         (match uu___5 with
                                          | (w', uu___6, uu___7) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu___5 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 let uu___6 =
                                   FStar_Syntax_Print.fv_to_string fv in
                                 not_implemented_warning uu___5 uu___6 msg);
                                FStar_Pervasives_Native.None))))