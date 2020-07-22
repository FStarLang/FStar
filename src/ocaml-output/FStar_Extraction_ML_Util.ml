open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____4 ->
    let uu____5 = FStar_Options.codegen () in
    uu____5 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
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
let (mlconst_of_const' :
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant) =
  fun sctt ->
    match sctt with
    | FStar_Const.Const_effect -> failwith "Unsupported constant"
    | FStar_Const.Const_range uu____55 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s, i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes, uu____80) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s, uu____86) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____87 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____88 ->
        failwith "Unhandled constant: real/reify/reflect"
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p ->
    fun c ->
      try (fun uu___51_100 -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___50_103 ->
          let uu____104 =
            let uu____105 = FStar_Range.string_of_range p in
            let uu____106 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____105 uu____106 in
          failwith uu____104
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r ->
    let cint i =
      let uu____118 =
        let uu____119 =
          let uu____120 =
            let uu____131 = FStar_Util.string_of_int i in
            (uu____131, FStar_Pervasives_Native.None) in
          FStar_Extraction_ML_Syntax.MLC_Int uu____120 in
        FStar_All.pipe_right uu____119
          (fun uu____142 -> FStar_Extraction_ML_Syntax.MLE_Const uu____142) in
      FStar_All.pipe_right uu____118
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty) in
    let cstr s =
      let uu____149 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun uu____150 -> FStar_Extraction_ML_Syntax.MLE_Const uu____150) in
      FStar_All.pipe_right uu____149
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty) in
    let uu____151 =
      let uu____158 =
        let uu____161 =
          let uu____162 = FStar_Range.file_of_range r in
          FStar_All.pipe_right uu____162 cstr in
        let uu____163 =
          let uu____166 =
            let uu____167 =
              let uu____168 = FStar_Range.start_of_range r in
              FStar_All.pipe_right uu____168 FStar_Range.line_of_pos in
            FStar_All.pipe_right uu____167 cint in
          let uu____169 =
            let uu____172 =
              let uu____173 =
                let uu____174 = FStar_Range.start_of_range r in
                FStar_All.pipe_right uu____174 FStar_Range.col_of_pos in
              FStar_All.pipe_right uu____173 cint in
            let uu____175 =
              let uu____178 =
                let uu____179 =
                  let uu____180 = FStar_Range.end_of_range r in
                  FStar_All.pipe_right uu____180 FStar_Range.line_of_pos in
                FStar_All.pipe_right uu____179 cint in
              let uu____181 =
                let uu____184 =
                  let uu____185 =
                    let uu____186 = FStar_Range.end_of_range r in
                    FStar_All.pipe_right uu____186 FStar_Range.col_of_pos in
                  FStar_All.pipe_right uu____185 cint in
                [uu____184] in
              uu____178 :: uu____181 in
            uu____172 :: uu____175 in
          uu____166 :: uu____169 in
        uu____161 :: uu____163 in
      (mk_range_mle, uu____158) in
    FStar_Extraction_ML_Syntax.MLE_App uu____151
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p ->
    fun c ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____200 ->
          let uu____201 = mlconst_of_const p c in
          FStar_Extraction_ML_Syntax.MLE_Const uu____201
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____225 =
            FStar_Util.find_opt
              (fun uu____239 ->
                 match uu____239 with | (y, uu____245) -> y = x) subst in
          (match uu____225 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
          let uu____262 =
            let uu____269 = subst_aux subst t1 in
            let uu____270 = subst_aux subst t2 in (uu____269, f, uu____270) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____262
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, path) ->
          let uu____277 =
            let uu____284 = FStar_List.map (subst_aux subst) args in
            (uu____284, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____277
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____292 = FStar_List.map (subst_aux subst) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____292
      | FStar_Extraction_ML_Syntax.MLTY_Top -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased -> t
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____307 ->
    fun args ->
      match uu____307 with
      | (formals, t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____318 =
               let uu____319 = FStar_List.zip formals args in
               subst_aux uu____319 t in
             FStar_Pervasives_Native.Some uu____318)
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts ->
    fun args ->
      let uu____348 = try_subst ts args in
      match uu____348 with
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
    fun uu___0_363 ->
      match uu___0_363 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, n) ->
          let uu____372 = FStar_Extraction_ML_UEnv.lookup_tydef g n in
          (match uu____372 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____378 = try_subst ts args in
               (match uu____378 with
                | FStar_Pervasives_Native.None ->
                    let uu____383 =
                      let uu____384 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n in
                      let uu____385 =
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu____386 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____384 uu____385 uu____386 in
                    failwith uu____383
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____390 -> FStar_Pervasives_Native.None)
      | uu____393 -> FStar_Pervasives_Native.None
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f ->
    fun f' ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE, uu____404) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST,
         FStar_Extraction_ML_Syntax.E_GHOST) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE,
         FStar_Extraction_ML_Syntax.E_IMPURE) -> true
      | uu____405 -> false
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___1_414 ->
    match uu___1_414 with
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
        | uu____430 ->
            let uu____435 =
              let uu____436 = FStar_Range.string_of_range r in
              let uu____437 = eff_to_string f in
              let uu____438 = eff_to_string f' in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____436
                uu____437 uu____438 in
            failwith uu____435
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
    (fun uu____475 ->
       fun t ->
         match uu____475 with
         | (uu____481, t0) ->
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
                | uu____585 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys, body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____617 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____624 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____624 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs, body);
                     FStar_Extraction_ML_Syntax.mlty = uu____634;
                     FStar_Extraction_ML_Syntax.loc = uu____635;_}
                   ->
                   let uu____656 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____656
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____669 = type_leq unfold_ty t2 t2' in
                        (if uu____669
                         then
                           let body1 =
                             let uu____677 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____677
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____679 =
                             let uu____682 =
                               let uu____683 =
                                 let uu____688 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____688 in
                               FStar_All.pipe_left uu____683
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu____682 in
                           (true, uu____679)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____717 =
                           let uu____724 =
                             let uu____727 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun uu____730 ->
                                  FStar_Pervasives_Native.Some uu____730)
                               uu____727 in
                           type_leq_c unfold_ty uu____724 t2 t2' in
                         match uu____717 with
                         | (ok, body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____749 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu____749
                               | uu____758 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____766 ->
                   let uu____769 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____769
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named (args, path),
             FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) ->
              if path = path'
              then
                let uu____799 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____799
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____812 = unfold_ty t in
                 match uu____812 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None ->
                     let uu____822 = unfold_ty t' in
                     (match uu____822 with
                      | FStar_Pervasives_Native.None ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple ts,
             FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____840 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____840
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top,
             FStar_Extraction_ML_Syntax.MLTY_Top) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____854, uu____855) ->
              let uu____862 = unfold_ty t in
              (match uu____862 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____872 -> (false, FStar_Pervasives_Native.None))
          | (uu____877, FStar_Extraction_ML_Syntax.MLTY_Named uu____878) ->
              let uu____885 = unfold_ty t' in
              (match uu____885 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____895 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased,
             FStar_Extraction_ML_Syntax.MLTY_Erased) -> (true, e)
          | uu____902 -> (false, FStar_Pervasives_Native.None)
and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        let uu____913 = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_All.pipe_right uu____913 FStar_Pervasives_Native.fst
let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
        let uu____936 =
          let uu____943 = erase_effect_annotations t1 in
          let uu____944 = erase_effect_annotations t2 in
          (uu____943, FStar_Extraction_ML_Syntax.E_PURE, uu____944) in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____936
    | uu____945 -> t
let is_type_abstraction :
  'a 'b 'c . (('a, 'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___2_971 ->
    match uu___2_971 with
    | (FStar_Util.Inl uu____982, uu____983)::uu____984 -> true
    | uu____1007 -> false
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1030 ->
    match uu____1030 with
    | (ns, n) ->
        let uu____1045 =
          let uu____1046 = FStar_Util.concat_l "." (FStar_List.append ns [n]) in
          FStar_Parser_Const.is_tuple_datacon_string uu____1046 in
        if uu____1045
        then
          let uu____1049 =
            let uu____1050 = FStar_Util.char_at n (Prims.of_int (7)) in
            FStar_Util.int_of_char uu____1050 in
          FStar_Pervasives_Native.Some uu____1049
        else FStar_Pervasives_Native.None
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) ->
        let uu____1063 = is_xtuple mlp in
        (match uu____1063 with
         | FStar_Pervasives_Native.Some n ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1067 -> e)
    | uu____1070 -> e
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___3_1079 ->
    match uu___3_1079 with
    | f::uu____1085 ->
        let uu____1088 =
          let uu____1095 = FStar_Ident.ns_of_lid f in
          FStar_Util.prefix uu____1095 in
        (match uu____1088 with
         | (ns, uu____1101) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id -> FStar_Ident.string_of_id id)))
    | uu____1112 -> failwith "impos"
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
             let uu____1157 =
               let uu____1158 = FStar_Ident.ident_of_lid f in
               FStar_Ident.string_of_id uu____1158 in
             (uu____1157, e)) fs vs
let (is_xtuple_ty :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1171 ->
    match uu____1171 with
    | (ns, n) ->
        let uu____1186 =
          let uu____1187 = FStar_Util.concat_l "." (FStar_List.append ns [n]) in
          FStar_Parser_Const.is_tuple_constructor_string uu____1187 in
        if uu____1186
        then
          let uu____1190 =
            let uu____1191 = FStar_Util.char_at n (Prims.of_int (5)) in
            FStar_Util.int_of_char uu____1191 in
          FStar_Pervasives_Native.Some uu____1190
        else FStar_Pervasives_Native.None
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) ->
        let uu____1204 = is_xtuple_ty mlp in
        (match uu____1204 with
         | FStar_Pervasives_Native.Some n ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1208 -> t)
    | uu____1211 -> t
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns -> FStar_String.concat "_" ns
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____1231 ->
    match uu____1231 with
    | (ns, n) -> FStar_String.concat "_" (FStar_List.append ns [n])
let (ml_module_name_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let mlp =
      let uu____1256 =
        let uu____1259 = FStar_All.pipe_right l FStar_Ident.ns_of_lid in
        FStar_All.pipe_right uu____1259
          (FStar_List.map FStar_Ident.string_of_id) in
      let uu____1268 =
        let uu____1269 = FStar_Ident.ident_of_lid l in
        FStar_Ident.string_of_id uu____1269 in
      (uu____1256, uu____1268) in
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
               (uu____1291, ("FStar"::"Ghost"::[], "erased")) -> true
           | FStar_Extraction_ML_Syntax.MLTY_Named
               (uu____1298, ("FStar"::"Tactics"::"Effect"::[], "tactic")) ->
               let uu____1305 = FStar_Options.codegen () in
               uu____1305 <>
                 (FStar_Pervasives_Native.Some FStar_Options.Plugin)
           | uu____1310 -> false) in
      let uu____1311 = erasableTypeNoDelta t in
      if uu____1311
      then true
      else
        (let uu____1313 = unfold_ty t in
         match uu____1313 with
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
            let uu____1332 =
              let uu____1339 = eraseTypeDeep unfold_ty tyd in
              let uu____1340 = eraseTypeDeep unfold_ty tycd in
              (uu____1339, etag, uu____1340) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1332
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) ->
          let uu____1348 = erasableType unfold_ty t in
          if uu____1348
          then FStar_Extraction_ML_Syntax.MLTY_Erased
          else
            (let uu____1350 =
               let uu____1357 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____1357, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1350)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1365 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1365
      | uu____1368 -> t
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1371 =
    let uu____1376 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____1376 in
  FStar_All.pipe_left uu____1371
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
          let uu____1449 = conjoin x y in
          FStar_Pervasives_Native.Some uu____1449
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____1461 = FStar_Range.file_of_range r in (line, uu____1461)
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1480, b) ->
        let uu____1482 = doms_and_cod b in
        (match uu____1482 with | (ds, c) -> ((a :: ds), c))
    | uu____1503 -> ([], t)
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t ->
    let uu____1515 = doms_and_cod t in FStar_Pervasives_Native.fst uu____1515
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1542, b) ->
        let uu____1544 = uncurry_mlty_fun b in
        (match uu____1544 with | (args, res) -> ((a :: args), res))
    | uu____1565 -> ([], t)
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | NoTacticEmbedding uu____1577 -> true
    | uu____1578 -> false
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | NoTacticEmbedding uu____1584 -> uu____1584
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r ->
    fun t ->
      fun msg ->
        let uu____1600 =
          let uu____1605 =
            let uu____1606 =
              let uu____1607 =
                let uu____1608 =
                  FStar_Errors.lookup
                    FStar_Errors.Warning_PluginNotImplemented in
                FStar_Errors.error_number uu____1608 in
              FStar_All.pipe_left FStar_Util.string_of_int uu____1607 in
            FStar_Util.format3
              "Plugin %s can not run natively because %s (use --warn_error -%s to carry on)."
              t msg uu____1606 in
          (FStar_Errors.Warning_PluginNotImplemented, uu____1605) in
        FStar_Errors.log_issue r uu____1600
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee ->
    match projectee with | Syntax_term -> true | uu____1620 -> false
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee ->
    match projectee with | Refl_emb -> true | uu____1626 -> false
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee -> match projectee with | NBE_t -> true | uu____1632 -> false
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee ->
    match projectee with | NBERefl_emb -> true | uu____1638 -> false
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
              let uu____1708 =
                let uu____1709 =
                  FStar_Extraction_ML_UEnv.mlpath_of_lident env l in
                FStar_Extraction_ML_Syntax.MLE_Name uu____1709 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1708 in
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
              let uu____1751 =
                let uu____1752 =
                  let uu____1759 = as_name (["FStar_Ident"], "lid_of_str") in
                  let uu____1762 =
                    let uu____1765 =
                      let uu____1766 =
                        let uu____1767 =
                          let uu____1768 = FStar_Ident.string_of_lid fv_lid in
                          FStar_Extraction_ML_Syntax.MLC_String uu____1768 in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____1767 in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1766 in
                    [uu____1765] in
                  (uu____1759, uu____1762) in
                FStar_Extraction_ML_Syntax.MLE_App uu____1752 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1751 in
            let emb_prefix uu___4_1781 =
              match uu___4_1781 with
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
                   | uu____1798 -> "mk_nbe_tactic_interpretation_" in
                 let uu____1799 =
                   let uu____1800 =
                     let uu____1801 = FStar_Util.string_of_int arity in
                     Prims.op_Hat idroot uu____1801 in
                   (["FStar_Tactics_InterpFuns"], uu____1800) in
                 as_name uu____1799) in
            let mk_from_tactic l arity =
              let idroot =
                match l with
                | Syntax_term -> "from_tactic_"
                | uu____1816 -> "from_nbe_tactic_" in
              let uu____1817 =
                let uu____1818 =
                  let uu____1819 = FStar_Util.string_of_int arity in
                  Prims.op_Hat idroot uu____1819 in
                (["FStar_Tactics_Native"], uu____1818) in
              as_name uu____1817 in
            let mk_basic_embedding l s =
              if s = "norm_step"
              then
                match l with
                | Syntax_term ->
                    as_name (["FStar_Tactics_Builtins"], "e_norm_step'")
                | NBE_t ->
                    as_name (["FStar_Tactics_Builtins"], "e_norm_step_nbe'")
                | uu____1837 ->
                    failwith "impossible: mk_basic_embedding norm_step"
              else emb_prefix l (Prims.op_Hat "e_" s) in
            let mk_arrow_as_prim_step l arity =
              let uu____1850 =
                let uu____1851 = FStar_Util.string_of_int arity in
                Prims.op_Hat "arrow_as_prim_step_" uu____1851 in
              emb_prefix l uu____1850 in
            let mk_any_embedding l s =
              let uu____1863 =
                let uu____1864 =
                  let uu____1871 = emb_prefix l "mk_any_emb" in
                  let uu____1872 =
                    let uu____1875 = str_to_name s in [uu____1875] in
                  (uu____1871, uu____1872) in
                FStar_Extraction_ML_Syntax.MLE_App uu____1864 in
              FStar_All.pipe_left w uu____1863 in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e)) in
            let emb_arrow l e1 e2 =
              let uu____1919 =
                let uu____1920 =
                  let uu____1927 = emb_prefix l "e_arrow" in
                  (uu____1927, [e1; e2]) in
                FStar_Extraction_ML_Syntax.MLE_App uu____1920 in
              FStar_All.pipe_left w uu____1919 in
            let known_type_constructors =
              let term_cs =
                let uu____1960 =
                  let uu____1973 =
                    let uu____1986 =
                      let uu____1999 =
                        let uu____2012 =
                          let uu____2025 =
                            let uu____2038 =
                              let uu____2051 =
                                let uu____2062 =
                                  let uu____2069 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.of_int (2))
                                      FStar_Range.dummyRange in
                                  (uu____2069, (Prims.of_int (2)), "tuple2") in
                                (uu____2062, Syntax_term) in
                              let uu____2076 =
                                let uu____2089 =
                                  let uu____2100 =
                                    let uu____2107 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term" in
                                    (uu____2107, Prims.int_zero, "term") in
                                  (uu____2100, Refl_emb) in
                                let uu____2114 =
                                  let uu____2127 =
                                    let uu____2138 =
                                      let uu____2145 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "sigelt" in
                                      (uu____2145, Prims.int_zero, "sigelt") in
                                    (uu____2138, Refl_emb) in
                                  let uu____2152 =
                                    let uu____2165 =
                                      let uu____2176 =
                                        let uu____2183 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "fv" in
                                        (uu____2183, Prims.int_zero, "fv") in
                                      (uu____2176, Refl_emb) in
                                    let uu____2190 =
                                      let uu____2203 =
                                        let uu____2214 =
                                          let uu____2221 =
                                            FStar_Reflection_Data.fstar_refl_types_lid
                                              "binder" in
                                          (uu____2221, Prims.int_zero,
                                            "binder") in
                                        (uu____2214, Refl_emb) in
                                      let uu____2228 =
                                        let uu____2241 =
                                          let uu____2252 =
                                            let uu____2259 =
                                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                                "binders" in
                                            (uu____2259, Prims.int_zero,
                                              "binders") in
                                          (uu____2252, Refl_emb) in
                                        let uu____2266 =
                                          let uu____2279 =
                                            let uu____2290 =
                                              let uu____2297 =
                                                FStar_Reflection_Data.fstar_refl_data_lid
                                                  "exp" in
                                              (uu____2297, Prims.int_zero,
                                                "exp") in
                                            (uu____2290, Refl_emb) in
                                          [uu____2279] in
                                        uu____2241 :: uu____2266 in
                                      uu____2203 :: uu____2228 in
                                    uu____2165 :: uu____2190 in
                                  uu____2127 :: uu____2152 in
                                uu____2089 :: uu____2114 in
                              uu____2051 :: uu____2076 in
                            ((FStar_Parser_Const.option_lid, Prims.int_one,
                               "option"), Syntax_term)
                              :: uu____2038 in
                          ((FStar_Parser_Const.list_lid, Prims.int_one,
                             "list"), Syntax_term)
                            :: uu____2025 in
                        ((FStar_Parser_Const.norm_step_lid, Prims.int_zero,
                           "norm_step"), Syntax_term)
                          :: uu____2012 in
                      ((FStar_Parser_Const.string_lid, Prims.int_zero,
                         "string"), Syntax_term)
                        :: uu____1999 in
                    ((FStar_Parser_Const.unit_lid, Prims.int_zero, "unit"),
                      Syntax_term) :: uu____1986 in
                  ((FStar_Parser_Const.bool_lid, Prims.int_zero, "bool"),
                    Syntax_term) :: uu____1973 in
                ((FStar_Parser_Const.int_lid, Prims.int_zero, "int"),
                  Syntax_term) :: uu____1960 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___5_2531 ->
                     match uu___5_2531 with
                     | (x, Syntax_term) -> (x, NBE_t)
                     | (x, Refl_emb) -> (x, NBERefl_emb)
                     | uu____2590 -> failwith "Impossible") term_cs in
              fun uu___6_2611 ->
                match uu___6_2611 with
                | Syntax_term -> term_cs
                | Refl_emb -> term_cs
                | uu____2624 -> nbe_cs in
            let is_known_type_constructor l fv1 n =
              FStar_Util.for_some
                (fun uu____2656 ->
                   match uu____2656 with
                   | ((x, args, uu____2669), uu____2670) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n = args))
                (known_type_constructors l) in
            let find_env_entry bv uu____2691 =
              match uu____2691 with
              | (bv', uu____2697) -> FStar_Syntax_Syntax.bv_eq bv bv' in
            let rec mk_embedding l env1 t2 =
              let t3 =
                FStar_TypeChecker_Normalize.unfold_whnf'
                  [FStar_TypeChecker_Env.ForExtraction] tcenv t2 in
              let uu____2727 =
                let uu____2728 = FStar_Syntax_Subst.compress t3 in
                uu____2728.FStar_Syntax_Syntax.n in
              match uu____2727 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env1 ->
                  let uu____2736 =
                    let uu____2737 =
                      let uu____2742 =
                        FStar_Util.find_opt (find_env_entry bv) env1 in
                      FStar_Util.must uu____2742 in
                    FStar_Pervasives_Native.snd uu____2737 in
                  FStar_All.pipe_left (mk_any_embedding l) uu____2736
              | FStar_Syntax_Syntax.Tm_refine (x, uu____2758) ->
                  mk_embedding l env1 x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4, uu____2764, uu____2765)
                  -> mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[], c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____2838 = FStar_Syntax_Subst.open_comp [b] c in
                  (match uu____2838 with
                   | (bs, c1) ->
                       let t0 =
                         let uu____2860 =
                           let uu____2861 = FStar_List.hd bs in
                           FStar_Pervasives_Native.fst uu____2861 in
                         uu____2860.FStar_Syntax_Syntax.sort in
                       let t11 = FStar_Syntax_Util.comp_result c1 in
                       let uu____2879 = mk_embedding l env1 t0 in
                       let uu____2880 = mk_embedding l env1 t11 in
                       emb_arrow l uu____2879 uu____2880)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs, c) ->
                  let tail =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      t3.FStar_Syntax_Syntax.pos in
                  let t4 =
                    let uu____2951 =
                      let uu____2952 =
                        let uu____2967 = FStar_Syntax_Syntax.mk_Total tail in
                        ([b], uu____2967) in
                      FStar_Syntax_Syntax.Tm_arrow uu____2952 in
                    FStar_Syntax_Syntax.mk uu____2951
                      t3.FStar_Syntax_Syntax.pos in
                  mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_fvar uu____2992 ->
                  let uu____2993 = FStar_Syntax_Util.head_and_args t3 in
                  (match uu____2993 with
                   | (head, args) ->
                       let n_args = FStar_List.length args in
                       let uu____3045 =
                         let uu____3046 = FStar_Syntax_Util.un_uinst head in
                         uu____3046.FStar_Syntax_Syntax.n in
                       (match uu____3045 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3072 ->
                                      match uu____3072 with
                                      | (t4, uu____3080) ->
                                          mk_embedding l env1 t4)) in
                            let nm =
                              let uu____3086 =
                                FStar_Ident.ident_of_lid
                                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                              FStar_Ident.string_of_id uu____3086 in
                            let uu____3087 =
                              let uu____3098 =
                                FStar_Util.find_opt
                                  (fun uu____3126 ->
                                     match uu____3126 with
                                     | ((x, uu____3138, uu____3139),
                                        uu____3140) ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l) in
                              FStar_All.pipe_right uu____3098 FStar_Util.must in
                            (match uu____3087 with
                             | ((uu____3179, t_arity, _trepr_head),
                                loc_embedding) ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm in
                                 (match t_arity with
                                  | uu____3190 when
                                      uu____3190 = Prims.int_zero -> head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu____3194 ->
                            let uu____3195 =
                              let uu____3196 =
                                let uu____3197 =
                                  FStar_Syntax_Print.term_to_string t3 in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____3197 in
                              NoTacticEmbedding uu____3196 in
                            FStar_Exn.raise uu____3195))
              | FStar_Syntax_Syntax.Tm_uinst uu____3198 ->
                  let uu____3205 = FStar_Syntax_Util.head_and_args t3 in
                  (match uu____3205 with
                   | (head, args) ->
                       let n_args = FStar_List.length args in
                       let uu____3257 =
                         let uu____3258 = FStar_Syntax_Util.un_uinst head in
                         uu____3258.FStar_Syntax_Syntax.n in
                       (match uu____3257 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3284 ->
                                      match uu____3284 with
                                      | (t4, uu____3292) ->
                                          mk_embedding l env1 t4)) in
                            let nm =
                              let uu____3298 =
                                FStar_Ident.ident_of_lid
                                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                              FStar_Ident.string_of_id uu____3298 in
                            let uu____3299 =
                              let uu____3310 =
                                FStar_Util.find_opt
                                  (fun uu____3338 ->
                                     match uu____3338 with
                                     | ((x, uu____3350, uu____3351),
                                        uu____3352) ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l) in
                              FStar_All.pipe_right uu____3310 FStar_Util.must in
                            (match uu____3299 with
                             | ((uu____3391, t_arity, _trepr_head),
                                loc_embedding) ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm in
                                 (match t_arity with
                                  | uu____3402 when
                                      uu____3402 = Prims.int_zero -> head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu____3406 ->
                            let uu____3407 =
                              let uu____3408 =
                                let uu____3409 =
                                  FStar_Syntax_Print.term_to_string t3 in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____3409 in
                              NoTacticEmbedding uu____3408 in
                            FStar_Exn.raise uu____3407))
              | FStar_Syntax_Syntax.Tm_app uu____3410 ->
                  let uu____3427 = FStar_Syntax_Util.head_and_args t3 in
                  (match uu____3427 with
                   | (head, args) ->
                       let n_args = FStar_List.length args in
                       let uu____3479 =
                         let uu____3480 = FStar_Syntax_Util.un_uinst head in
                         uu____3480.FStar_Syntax_Syntax.n in
                       (match uu____3479 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3506 ->
                                      match uu____3506 with
                                      | (t4, uu____3514) ->
                                          mk_embedding l env1 t4)) in
                            let nm =
                              let uu____3520 =
                                FStar_Ident.ident_of_lid
                                  (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                              FStar_Ident.string_of_id uu____3520 in
                            let uu____3521 =
                              let uu____3532 =
                                FStar_Util.find_opt
                                  (fun uu____3560 ->
                                     match uu____3560 with
                                     | ((x, uu____3572, uu____3573),
                                        uu____3574) ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l) in
                              FStar_All.pipe_right uu____3532 FStar_Util.must in
                            (match uu____3521 with
                             | ((uu____3613, t_arity, _trepr_head),
                                loc_embedding) ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm in
                                 (match t_arity with
                                  | uu____3624 when
                                      uu____3624 = Prims.int_zero -> head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu____3628 ->
                            let uu____3629 =
                              let uu____3630 =
                                let uu____3631 =
                                  FStar_Syntax_Print.term_to_string t3 in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____3631 in
                              NoTacticEmbedding uu____3630 in
                            FStar_Exn.raise uu____3629))
              | uu____3632 ->
                  let uu____3633 =
                    let uu____3634 =
                      let uu____3635 = FStar_Syntax_Print.term_to_string t3 in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____3635 in
                    NoTacticEmbedding uu____3634 in
                  FStar_Exn.raise uu____3633 in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____3652 =
                      let uu____3653 =
                        let uu____3660 =
                          as_name (["FStar_Syntax_Embeddings"], "debug_wrap") in
                        let uu____3663 =
                          let uu____3666 =
                            let uu____3667 =
                              let uu____3668 =
                                let uu____3669 =
                                  FStar_Ident.string_of_lid fv_lid in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____3669 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____3668 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____3667 in
                          let uu____3670 =
                            let uu____3673 =
                              let uu____3674 =
                                let uu____3675 =
                                  let uu____3676 =
                                    let uu____3683 =
                                      let uu____3686 = str_to_name "args" in
                                      [uu____3686] in
                                    (body, uu____3683) in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3676 in
                                FStar_All.pipe_left w uu____3675 in
                              mk_lam "_" uu____3674 in
                            [uu____3673] in
                          uu____3666 :: uu____3670 in
                        (uu____3660, uu____3663) in
                      FStar_Extraction_ML_Syntax.MLE_App uu____3653 in
                    FStar_All.pipe_left w uu____3652 in
                  mk_lam "args" body1
              | uu____3691 ->
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
                    let uu____3728 =
                      let uu____3729 =
                        let uu____3730 =
                          let uu____3737 =
                            let uu____3740 = as_name ([], "args") in
                            [uu____3740] in
                          (body, uu____3737) in
                        FStar_Extraction_ML_Syntax.MLE_App uu____3730 in
                      FStar_All.pipe_left w uu____3729 in
                    (pattern, FStar_Pervasives_Native.None, uu____3728) in
                  let default_branch =
                    let uu____3756 =
                      let uu____3757 =
                        let uu____3758 =
                          let uu____3765 = str_to_name "failwith" in
                          let uu____3766 =
                            let uu____3769 =
                              let uu____3770 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange)) in
                              FStar_All.pipe_left w uu____3770 in
                            [uu____3769] in
                          (uu____3765, uu____3766) in
                        FStar_Extraction_ML_Syntax.MLE_App uu____3758 in
                      FStar_All.pipe_left w uu____3757 in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____3756) in
                  let body1 =
                    let uu____3776 =
                      let uu____3777 =
                        let uu____3792 = as_name ([], "args") in
                        (uu____3792, [branch; default_branch]) in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____3777 in
                    FStar_All.pipe_left w uu____3776 in
                  let body2 =
                    let uu____3830 =
                      let uu____3831 =
                        let uu____3838 =
                          as_name (["FStar_Syntax_Embeddings"], "debug_wrap") in
                        let uu____3841 =
                          let uu____3844 =
                            let uu____3845 =
                              let uu____3846 =
                                let uu____3847 =
                                  FStar_Ident.string_of_lid fv_lid in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____3847 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____3846 in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____3845 in
                          let uu____3848 =
                            let uu____3851 = mk_lam "_" body1 in [uu____3851] in
                          uu____3844 :: uu____3848 in
                        (uu____3838, uu____3841) in
                      FStar_Extraction_ML_Syntax.MLE_App uu____3831 in
                    FStar_All.pipe_left w uu____3830 in
                  mk_lam "args" body2 in
            let uu____3854 = FStar_Syntax_Util.arrow_formals_comp t1 in
            match uu____3854 with
            | (bs, c) ->
                let uu____3863 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None -> (bs, c)
                  | FStar_Pervasives_Native.Some n ->
                      let n_bs = FStar_List.length bs in
                      if n = n_bs
                      then (bs, c)
                      else
                        if n < n_bs
                        then
                          (let uu____3949 = FStar_Util.first_N n bs in
                           match uu____3949 with
                           | (bs1, rest) ->
                               let c1 =
                                 let uu____4027 =
                                   FStar_Syntax_Util.arrow rest c in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____4027 in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____4042 =
                               FStar_Ident.string_of_lid fv_lid in
                             let uu____4043 = FStar_Util.string_of_int n in
                             let uu____4044 = FStar_Util.string_of_int n_bs in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____4042 uu____4043 uu____4044 in
                           FStar_Exn.raise (NoTacticEmbedding msg)) in
                (match uu____3863 with
                 | (bs1, c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1 in
                     let arity = FStar_List.length bs1 in
                     let uu____4093 =
                       let uu____4114 =
                         FStar_Util.prefix_until
                           (fun uu____4156 ->
                              match uu____4156 with
                              | (b, uu____4164) ->
                                  let uu____4169 =
                                    let uu____4170 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort in
                                    uu____4170.FStar_Syntax_Syntax.n in
                                  (match uu____4169 with
                                   | FStar_Syntax_Syntax.Tm_type uu____4173
                                       -> false
                                   | uu____4174 -> true)) bs1 in
                       match uu____4114 with
                       | FStar_Pervasives_Native.None -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars, x, rest) ->
                           (tvars, (x :: rest)) in
                     (match uu____4093 with
                      | (type_vars, bs2) ->
                          let tvar_arity = FStar_List.length type_vars in
                          let non_tvar_arity = FStar_List.length bs2 in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i ->
                                 fun tv ->
                                   let uu____4412 =
                                     FStar_Util.string_of_int i in
                                   Prims.op_Hat "tv_" uu____4412) type_vars in
                          let tvar_context =
                            FStar_List.map2
                              (fun b ->
                                 fun nm ->
                                   ((FStar_Pervasives_Native.fst b), nm))
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
                                let uu____4501 =
                                  FStar_Syntax_Util.is_pure_comp c1 in
                                if uu____4501
                                then
                                  let cb = str_to_name "cb" in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity in
                                  let args =
                                    let uu____4513 =
                                      let uu____4516 =
                                        let uu____4519 = lid_to_name fv_lid1 in
                                        let uu____4520 =
                                          let uu____4523 =
                                            let uu____4524 =
                                              let uu____4525 =
                                                let uu____4526 =
                                                  let uu____4537 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity in
                                                  (uu____4537,
                                                    FStar_Pervasives_Native.None) in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____4526 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____4525 in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____4524 in
                                          [uu____4523; fv_lid_embedded; cb] in
                                        uu____4519 :: uu____4520 in
                                      res_embedding :: uu____4516 in
                                    FStar_List.append arg_unembeddings
                                      uu____4513 in
                                  let fun_embedding =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (embed_fun_N, args)) in
                                  let tabs =
                                    abstract_tvars tvar_names fun_embedding in
                                  let cb_tabs = mk_lam "cb" tabs in
                                  let uu____4553 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs in
                                  (uu____4553, arity, true)
                                else
                                  (let uu____4556 =
                                     let uu____4557 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1) in
                                     FStar_Ident.lid_equals uu____4557
                                       FStar_Parser_Const.effect_TAC_lid in
                                   if uu____4556
                                   then
                                     let h =
                                       mk_tactic_interpretation loc
                                         non_tvar_arity in
                                     let tac_fun =
                                       let uu____4566 =
                                         let uu____4567 =
                                           let uu____4574 =
                                             mk_from_tactic loc
                                               non_tvar_arity in
                                           let uu____4575 =
                                             let uu____4578 =
                                               lid_to_name fv_lid1 in
                                             [uu____4578] in
                                           (uu____4574, uu____4575) in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____4567 in
                                       FStar_All.pipe_left w uu____4566 in
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
                                           let uu____4588 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args]))) in
                                           mk_lam "args" uu____4588
                                       | uu____4591 ->
                                           let uu____4594 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args)) in
                                           abstract_tvars tvar_names
                                             uu____4594 in
                                     let uu____4597 =
                                       let uu____4598 = mk_lam "ncb" tabs in
                                       mk_lam "psc" uu____4598 in
                                     (uu____4597, (arity + Prims.int_one),
                                       false)
                                   else
                                     (let uu____4600 =
                                        let uu____4601 =
                                          let uu____4602 =
                                            FStar_Syntax_Print.term_to_string
                                              t1 in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____4602 in
                                        NoTacticEmbedding uu____4601 in
                                      FStar_Exn.raise uu____4600))
                            | (b, uu____4610)::bs4 ->
                                let uu____4630 =
                                  let uu____4633 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort in
                                  uu____4633 :: accum_embeddings in
                                aux loc uu____4630 bs4 in
                          (try
                             (fun uu___713_4653 ->
                                match () with
                                | () ->
                                    let uu____4664 = aux Syntax_term [] bs2 in
                                    (match uu____4664 with
                                     | (w1, a, b) ->
                                         let uu____4684 = aux NBE_t [] bs2 in
                                         (match uu____4684 with
                                          | (w', uu____4702, uu____4703) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____4728 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 let uu____4729 =
                                   FStar_Syntax_Print.fv_to_string fv in
                                 not_implemented_warning uu____4728
                                   uu____4729 msg);
                                FStar_Pervasives_Native.None))))