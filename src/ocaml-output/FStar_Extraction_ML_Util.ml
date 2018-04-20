open Prims
let (codegen_fsharp : Prims.unit -> Prims.bool) =
  fun uu____3 ->
    let uu____4 = FStar_Options.codegen () in
    uu____4 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
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
    | FStar_Const.Const_range uu____49 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s, i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes, uu____74) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s, uu____80) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify -> failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____81 ->
        failwith "Unhandled constant: reify/reflect"
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p ->
    fun c ->
      try mlconst_of_const' c
      with
      | uu____94 ->
          let uu____95 =
            let uu____96 = FStar_Range.string_of_range p in
            let uu____97 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____96 uu____97 in
          failwith uu____95
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r ->
    let cint i =
      let uu____105 =
        let uu____106 =
          let uu____107 =
            let uu____118 = FStar_Util.string_of_int i in
            (uu____118, FStar_Pervasives_Native.None) in
          FStar_Extraction_ML_Syntax.MLC_Int uu____107 in
        FStar_All.pipe_right uu____106
          (fun _0_41 -> FStar_Extraction_ML_Syntax.MLE_Const _0_41) in
      FStar_All.pipe_right uu____105
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty) in
    let cstr s =
      let uu____133 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_42 -> FStar_Extraction_ML_Syntax.MLE_Const _0_42) in
      FStar_All.pipe_right uu____133
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty) in
    let uu____134 =
      let uu____141 =
        let uu____144 =
          let uu____145 = FStar_Range.file_of_range r in
          FStar_All.pipe_right uu____145 cstr in
        let uu____146 =
          let uu____149 =
            let uu____150 =
              let uu____151 = FStar_Range.start_of_range r in
              FStar_All.pipe_right uu____151 FStar_Range.line_of_pos in
            FStar_All.pipe_right uu____150 cint in
          let uu____152 =
            let uu____155 =
              let uu____156 =
                let uu____157 = FStar_Range.start_of_range r in
                FStar_All.pipe_right uu____157 FStar_Range.col_of_pos in
              FStar_All.pipe_right uu____156 cint in
            let uu____158 =
              let uu____161 =
                let uu____162 =
                  let uu____163 = FStar_Range.end_of_range r in
                  FStar_All.pipe_right uu____163 FStar_Range.line_of_pos in
                FStar_All.pipe_right uu____162 cint in
              let uu____164 =
                let uu____167 =
                  let uu____168 =
                    let uu____169 = FStar_Range.end_of_range r in
                    FStar_All.pipe_right uu____169 FStar_Range.col_of_pos in
                  FStar_All.pipe_right uu____168 cint in
                [uu____167] in
              uu____161 :: uu____164 in
            uu____155 :: uu____158 in
          uu____149 :: uu____152 in
        uu____144 :: uu____146 in
      (mk_range_mle, uu____141) in
    FStar_Extraction_ML_Syntax.MLE_App uu____134
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p ->
    fun c ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____179 ->
          let uu____180 = mlconst_of_const p c in
          FStar_Extraction_ML_Syntax.MLE_Const uu____180
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident, FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1 ->
    fun t ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____200 =
            FStar_Util.find_opt
              (fun uu____214 ->
                 match uu____214 with | (y, uu____220) -> y = x) subst1 in
          (match uu____200 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
          let uu____237 =
            let uu____244 = subst_aux subst1 t1 in
            let uu____245 = subst_aux subst1 t2 in (uu____244, f, uu____245) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____237
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, path) ->
          let uu____252 =
            let uu____259 = FStar_List.map (subst_aux subst1) args in
            (uu____259, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____252
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____267 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____267
      | FStar_Extraction_ML_Syntax.MLTY_Top ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____278 ->
    fun args ->
      match uu____278 with
      | (formals, t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____289 =
               let uu____290 = FStar_List.zip formals args in
               subst_aux uu____290 t in
             FStar_Pervasives_Native.Some uu____289)
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents, FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts ->
    fun args ->
      let uu____315 = try_subst ts args in
      match uu____315 with
      | FStar_Pervasives_Native.None ->
          failwith
            "Substitution must be fully applied (see GitHub issue #490)"
      | FStar_Pervasives_Native.Some t -> t
let (udelta_unfold :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun g ->
    fun uu___62_326 ->
      match uu___62_326 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, n1) ->
          let uu____335 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____335 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____341 = try_subst ts args in
               (match uu____341 with
                | FStar_Pervasives_Native.None ->
                    let uu____346 =
                      let uu____347 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1 in
                      let uu____348 =
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu____349 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____347 uu____348 uu____349 in
                    failwith uu____346
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____353 -> FStar_Pervasives_Native.None)
      | uu____356 -> FStar_Pervasives_Native.None
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f ->
    fun f' ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE, uu____363) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST,
         FStar_Extraction_ML_Syntax.E_GHOST) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE,
         FStar_Extraction_ML_Syntax.E_IMPURE) -> true
      | uu____364 -> false
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___63_371 ->
    match uu___63_371 with
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
        | uu____381 ->
            let uu____386 =
              let uu____387 = FStar_Range.string_of_range r in
              let uu____388 = eff_to_string f in
              let uu____389 = eff_to_string f' in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____387
                uu____388 uu____389 in
            failwith uu____386
let (join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r ->
    fun fs ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let (mk_ty_fun :
  (FStar_Extraction_ML_Syntax.mlident, FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  FStar_List.fold_right
    (fun uu____418 ->
       fun t ->
         match uu____418 with
         | (uu____424, t0) ->
             FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option[@@deriving
                                                                    show]
let rec (type_leq_c :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,
            FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2)
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
                | uu____511 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys, body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____543 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____550 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____550 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs, body);
                     FStar_Extraction_ML_Syntax.mlty = uu____560;
                     FStar_Extraction_ML_Syntax.loc = uu____561;_}
                   ->
                   let uu____582 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____582
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____598 = type_leq unfold_ty t2 t2' in
                        (if uu____598
                         then
                           let body1 =
                             let uu____609 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____609
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____614 =
                             let uu____617 =
                               let uu____618 =
                                 let uu____621 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____621 in
                               FStar_All.pipe_left uu____618
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu____617 in
                           (true, uu____614)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____650 =
                           let uu____657 =
                             let uu____660 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun _0_43 ->
                                  FStar_Pervasives_Native.Some _0_43)
                               uu____660 in
                           type_leq_c unfold_ty uu____657 t2 t2' in
                         match uu____650 with
                         | (ok, body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____684 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu____684
                               | uu____693 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____701 ->
                   let uu____704 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____704
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named (args, path),
             FStar_Extraction_ML_Syntax.MLTY_Named (args', path')) ->
              if path = path'
              then
                let uu____740 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____740
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____756 = unfold_ty t in
                 match uu____756 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None ->
                     let uu____770 = unfold_ty t' in
                     (match uu____770 with
                      | FStar_Pervasives_Native.None ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple ts,
             FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____792 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____792
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top,
             FStar_Extraction_ML_Syntax.MLTY_Top) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____809, uu____810) ->
              let uu____817 = unfold_ty t in
              (match uu____817 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____831 -> (false, FStar_Pervasives_Native.None))
          | (uu____836, FStar_Extraction_ML_Syntax.MLTY_Named uu____837) ->
              let uu____844 = unfold_ty t' in
              (match uu____844 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____858 -> (false, FStar_Pervasives_Native.None))
          | uu____863 -> (false, FStar_Pervasives_Native.None)
and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        let uu____874 = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_All.pipe_right uu____874 FStar_Pervasives_Native.fst
let is_type_abstraction :
  'a 'b 'c .
    (('a, 'b) FStar_Util.either, 'c) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.bool
  =
  fun uu___64_912 ->
    match uu___64_912 with
    | (FStar_Util.Inl uu____923, uu____924)::uu____925 -> true
    | uu____948 -> false
let (is_xtuple :
  (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____969 ->
    match uu____969 with
    | (ns, n1) ->
        let uu____984 =
          let uu____985 = FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_datacon_string uu____985 in
        if uu____984
        then
          let uu____988 =
            let uu____989 = FStar_Util.char_at n1 (Prims.parse_int "7") in
            FStar_Util.int_of_char uu____989 in
          FStar_Pervasives_Native.Some uu____988
        else FStar_Pervasives_Native.None
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp, args) ->
        let uu____1000 = is_xtuple mlp in
        (match uu____1000 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1004 -> e)
    | uu____1007 -> e
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___65_1014 ->
    match uu___65_1014 with
    | f::uu____1020 ->
        let uu____1023 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____1023 with
         | (ns, uu____1033) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1 -> id1.FStar_Ident.idText)))
    | uu____1044 -> failwith "impos"
let record_fields :
  'a .
    FStar_Ident.lident Prims.list ->
      'a Prims.list ->
        (Prims.string, 'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs ->
    fun vs ->
      FStar_List.map2
        (fun f -> fun e -> (((f.FStar_Ident.ident).FStar_Ident.idText), e))
        fs vs
let (is_xtuple_ty :
  (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1093 ->
    match uu____1093 with
    | (ns, n1) ->
        let uu____1108 =
          let uu____1109 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_constructor_string uu____1109 in
        if uu____1108
        then
          let uu____1112 =
            let uu____1113 = FStar_Util.char_at n1 (Prims.parse_int "5") in
            FStar_Util.int_of_char uu____1113 in
          FStar_Pervasives_Native.Some uu____1112
        else FStar_Pervasives_Native.None
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args, mlp) ->
        let uu____1124 = is_xtuple_ty mlp in
        (match uu____1124 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1128 -> t)
    | uu____1131 -> t
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns ->
    let uu____1139 = codegen_fsharp () in
    if uu____1139
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let (flatten_mlpath :
  (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1149 ->
    match uu____1149 with
    | (ns, n1) ->
        let uu____1162 = codegen_fsharp () in
        if uu____1162
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l ->
    let uu____1173 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i -> i.FStar_Ident.idText)) in
    (uu____1173, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty ->
    fun t ->
      let uu____1193 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t in
      if uu____1193
      then true
      else
        (let uu____1195 = unfold_ty t in
         match uu____1195 with
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
            let uu____1215 =
              let uu____1222 = eraseTypeDeep unfold_ty tyd in
              let uu____1226 = eraseTypeDeep unfold_ty tycd in
              (uu____1222, etag, uu____1226) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1215
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty, mlp) ->
          let uu____1237 = erasableType unfold_ty t in
          if uu____1237
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1242 =
               let uu____1249 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____1249, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1242)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1260 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1260
      | uu____1266 -> t
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1269 =
    let uu____1272 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____1272 in
  FStar_All.pipe_left uu____1269
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
          let uu____1337 = conjoin x y in
          FStar_Pervasives_Native.Some uu____1337
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int, Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____1347 = FStar_Range.file_of_range r in (line, uu____1347)
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,
      FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1364, b) ->
        let uu____1366 = doms_and_cod b in
        (match uu____1366 with | (ds, c) -> ((a :: ds), c))
    | uu____1387 -> ([], t)
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t ->
    let uu____1397 = doms_and_cod t in FStar_Pervasives_Native.fst uu____1397
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,
      FStar_Extraction_ML_Syntax.mlty) FStar_Pervasives_Native.tuple2)
  =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a, uu____1422, b) ->
        let uu____1424 = uncurry_mlty_fun b in
        (match uu____1424 with | (args, res) -> ((a :: args), res))
    | uu____1445 -> ([], t)
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | NoTacticEmbedding uu____1454 -> true
    | uu____1455 -> false
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | NoTacticEmbedding uu____1462 -> uu____1462
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> Prims.unit) =
  fun r ->
    fun t ->
      fun msg ->
        let uu____1472 =
          let uu____1477 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1477) in
        FStar_Errors.log_issue r uu____1472
type emb_decl =
  | Embed 
  | Unembed [@@deriving show]
let (uu___is_Embed : emb_decl -> Prims.bool) =
  fun projectee -> match projectee with | Embed -> true | uu____1481 -> false
let (uu___is_Unembed : emb_decl -> Prims.bool) =
  fun projectee ->
    match projectee with | Unembed -> true | uu____1485 -> false
type emb_loc =
  | S 
  | R [@@deriving show]
let (uu___is_S : emb_loc -> Prims.bool) =
  fun projectee -> match projectee with | S -> true | uu____1489 -> false
let (uu___is_R : emb_loc -> Prims.bool) =
  fun projectee -> match projectee with | R -> true | uu____1493 -> false
type embedding =
  {
  embed: FStar_Extraction_ML_Syntax.mlexpr ;
  unembed: FStar_Extraction_ML_Syntax.mlexpr ;
  type_repr: FStar_Extraction_ML_Syntax.mlexpr }[@@deriving show]
let (__proj__Mkembedding__item__embed :
  embedding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee ->
    match projectee with
    | { embed = __fname__embed; unembed = __fname__unembed;
        type_repr = __fname__type_repr;_} -> __fname__embed
let (__proj__Mkembedding__item__unembed :
  embedding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee ->
    match projectee with
    | { embed = __fname__embed; unembed = __fname__unembed;
        type_repr = __fname__type_repr;_} -> __fname__unembed
let (__proj__Mkembedding__item__type_repr :
  embedding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee ->
    match projectee with
    | { embed = __fname__embed; unembed = __fname__unembed;
        type_repr = __fname__type_repr;_} -> __fname__type_repr
type variance =
  | Covariant 
  | Contravariant 
  | Invariant [@@deriving show]
let (uu___is_Covariant : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | Covariant -> true | uu____1527 -> false
let (uu___is_Contravariant : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | Contravariant -> true | uu____1531 -> false
let (uu___is_Invariant : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | Invariant -> true | uu____1535 -> false
let (interpret_plugin_as_term_fun :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mlexpr' ->
          (FStar_Extraction_ML_Syntax.mlexpr, Prims.int, Prims.bool)
            FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun tcenv ->
    fun fv ->
      fun t ->
        fun ml_fv ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant] tcenv t in
          let w =
            FStar_Extraction_ML_Syntax.with_ty
              FStar_Extraction_ML_Syntax.MLTY_Top in
          let lid_to_name l =
            let uu____1564 =
              let uu____1565 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1565 in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1564 in
          let lid_to_top_name l =
            let uu____1570 =
              let uu____1571 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1571 in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1570 in
          let str_to_name s =
            let uu____1576 = FStar_Ident.lid_of_str s in
            lid_to_name uu____1576 in
          let str_to_top_name s =
            let uu____1581 = FStar_Ident.lid_of_str s in
            lid_to_top_name uu____1581 in
          let fstar_syn_syn_prefix s =
            str_to_name (Prims.strcat "FStar_Syntax_Syntax." s) in
          let fstar_refl_data_prefix s =
            str_to_name (Prims.strcat "FStar_Reflection_Data." s) in
          let fstar_syn_emb_prefix s =
            str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s) in
          let fstar_refl_emb_prefix s =
            str_to_name (Prims.strcat "FStar_Reflection_Embeddings." s) in
          let mk_basic_embedding m l s =
            let emb_fun =
              match l with
              | S -> fstar_syn_emb_prefix
              | R -> fstar_refl_emb_prefix in
            match m with
            | Embed -> emb_fun (Prims.strcat "embed_" s)
            | Unembed -> emb_fun (Prims.strcat "unembed_" s) in
          let mk_lam nm e =
            FStar_All.pipe_left w
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e)) in
          let id_embedding nm =
            let uu____1638 = mk_basic_embedding Embed S "any" in
            let uu____1639 = mk_basic_embedding Unembed S "any" in
            let uu____1640 = str_to_name nm in
            {
              embed = uu____1638;
              unembed = uu____1639;
              type_repr = uu____1640
            } in
          let known_type_constructors =
            let uu____1654 =
              let uu____1665 = fstar_syn_syn_prefix "t_int" in
              (FStar_Parser_Const.int_lid, [], uu____1665, S) in
            let uu____1668 =
              let uu____1681 =
                let uu____1692 = fstar_syn_syn_prefix "t_bool" in
                (FStar_Parser_Const.bool_lid, [], uu____1692, S) in
              let uu____1695 =
                let uu____1708 =
                  let uu____1719 = fstar_syn_syn_prefix "t_unit" in
                  (FStar_Parser_Const.unit_lid, [], uu____1719, S) in
                let uu____1722 =
                  let uu____1735 =
                    let uu____1746 = fstar_syn_syn_prefix "t_string" in
                    (FStar_Parser_Const.string_lid, [], uu____1746, S) in
                  let uu____1749 =
                    let uu____1762 =
                      let uu____1773 =
                        FStar_Reflection_Data.fstar_refl_types_lid "term" in
                      let uu____1774 = fstar_syn_syn_prefix "t_term" in
                      (uu____1773, [], uu____1774, R) in
                    let uu____1777 =
                      let uu____1790 =
                        let uu____1801 =
                          FStar_Reflection_Data.fstar_refl_types_lid "fv" in
                        let uu____1802 = fstar_syn_syn_prefix "t_fv" in
                        (uu____1801, [], uu____1802, R) in
                      let uu____1805 =
                        let uu____1818 =
                          let uu____1829 =
                            FStar_Reflection_Data.fstar_refl_types_lid
                              "binder" in
                          let uu____1830 = fstar_syn_syn_prefix "t_binder" in
                          (uu____1829, [], uu____1830, R) in
                        let uu____1833 =
                          let uu____1846 =
                            let uu____1857 =
                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                "binders" in
                            let uu____1858 = fstar_syn_syn_prefix "t_binders" in
                            (uu____1857, [], uu____1858, R) in
                          let uu____1861 =
                            let uu____1874 =
                              let uu____1885 =
                                fstar_syn_syn_prefix "t_norm_step" in
                              (FStar_Parser_Const.norm_step_lid, [],
                                uu____1885, S) in
                            let uu____1888 =
                              let uu____1901 =
                                let uu____1912 =
                                  fstar_syn_syn_prefix "t_list_of" in
                                (FStar_Parser_Const.list_lid, [Covariant],
                                  uu____1912, S) in
                              let uu____1915 =
                                let uu____1928 =
                                  let uu____1939 =
                                    fstar_syn_syn_prefix "t_option_of" in
                                  (FStar_Parser_Const.option_lid,
                                    [Covariant], uu____1939, S) in
                                let uu____1942 =
                                  let uu____1955 =
                                    let uu____1966 =
                                      FStar_Parser_Const.mk_tuple_lid
                                        (Prims.parse_int "2")
                                        FStar_Range.dummyRange in
                                    let uu____1967 =
                                      fstar_syn_syn_prefix "t_tuple2_of" in
                                    (uu____1966, [Covariant; Covariant],
                                      uu____1967, S) in
                                  let uu____1970 =
                                    let uu____1983 =
                                      let uu____1994 =
                                        FStar_Reflection_Data.fstar_refl_data_lid
                                          "exp" in
                                      let uu____1995 =
                                        fstar_refl_data_prefix "t_exp" in
                                      (uu____1994, [], uu____1995, R) in
                                    [uu____1983] in
                                  uu____1955 :: uu____1970 in
                                uu____1928 :: uu____1942 in
                              uu____1901 :: uu____1915 in
                            uu____1874 :: uu____1888 in
                          uu____1846 :: uu____1861 in
                        uu____1818 :: uu____1833 in
                      uu____1790 :: uu____1805 in
                    uu____1762 :: uu____1777 in
                  uu____1735 :: uu____1749 in
                uu____1708 :: uu____1722 in
              uu____1681 :: uu____1695 in
            uu____1654 :: uu____1668 in
          let is_known_type_constructor fv1 n1 =
            FStar_Util.for_some
              (fun uu____2164 ->
                 match uu____2164 with
                 | (x, args, uu____2177, uu____2178) ->
                     (FStar_Syntax_Syntax.fv_eq_lid fv1 x) &&
                       (n1 = (FStar_List.length args)))
              known_type_constructors in
          let embed_type_app fv1 arg_embeddings =
            let nm =
              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText in
            let uu____2199 =
              let uu____2210 =
                FStar_Util.find_opt
                  (fun uu____2238 ->
                     match uu____2238 with
                     | (x, uu____2250, uu____2251, uu____2252) ->
                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                  known_type_constructors in
              FStar_All.pipe_right uu____2210 FStar_Util.must in
            match uu____2199 with
            | (uu____2289, variances, trepr_head, loc_embedding) ->
                let choose1 e_or_u variance embedding =
                  match variance with
                  | Covariant ->
                      (match e_or_u with
                       | Embed -> [embedding.embed; embedding.type_repr]
                       | Unembed -> [embedding.unembed])
                  | Contravariant ->
                      (match e_or_u with
                       | Embed -> [embedding.unembed]
                       | Unembed -> [embedding.embed; embedding.type_repr])
                  | Invariant ->
                      [embedding.embed;
                      embedding.type_repr;
                      embedding.unembed] in
                let mk1 embed_or_unembed =
                  let head1 =
                    mk_basic_embedding embed_or_unembed loc_embedding nm in
                  match variances with
                  | [] -> head1
                  | uu____2320 ->
                      let args =
                        FStar_List.map2 (choose1 embed_or_unembed) variances
                          arg_embeddings in
                      FStar_All.pipe_left w
                        (FStar_Extraction_ML_Syntax.MLE_App
                           (head1, (FStar_List.flatten args))) in
                let type_repr =
                  match variances with
                  | [] -> trepr_head
                  | uu____2333 ->
                      let uu____2336 =
                        let uu____2337 =
                          let uu____2344 =
                            FStar_List.map (fun x -> x.type_repr)
                              arg_embeddings in
                          (trepr_head, uu____2344) in
                        FStar_Extraction_ML_Syntax.MLE_App uu____2337 in
                      FStar_All.pipe_left w uu____2336 in
                let uu____2351 = mk1 Embed in
                let uu____2352 = mk1 Unembed in
                { embed = uu____2351; unembed = uu____2352; type_repr } in
          let find_env_entry bv uu____2363 =
            match uu____2363 with
            | (bv', uu____2369) -> FStar_Syntax_Syntax.bv_eq bv bv' in
          let rec mk_embedding env t2 =
            let uu____2389 =
              let uu____2390 = FStar_Syntax_Subst.compress t2 in
              uu____2390.FStar_Syntax_Syntax.n in
            match uu____2389 with
            | FStar_Syntax_Syntax.Tm_name bv when
                FStar_Util.for_some (find_env_entry bv) env ->
                let uu____2398 =
                  let uu____2403 =
                    FStar_Util.find_opt (find_env_entry bv) env in
                  FStar_Util.must uu____2403 in
                FStar_Pervasives_Native.snd uu____2398
            | FStar_Syntax_Syntax.Tm_refine (x, uu____2419) ->
                mk_embedding env x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t3, uu____2425, uu____2426) ->
                mk_embedding env t3
            | uu____2467 ->
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2 in
                let uu____2469 = FStar_Syntax_Util.head_and_args t3 in
                (match uu____2469 with
                 | (head1, args) ->
                     let n_args = FStar_List.length args in
                     let uu____2513 =
                       let uu____2514 = FStar_Syntax_Util.un_uinst head1 in
                       uu____2514.FStar_Syntax_Syntax.n in
                     (match uu____2513 with
                      | FStar_Syntax_Syntax.Tm_refine (b, uu____2518) ->
                          mk_embedding env b.FStar_Syntax_Syntax.sort
                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                          is_known_type_constructor fv1 n_args ->
                          let arg_embeddings =
                            FStar_List.map
                              (fun uu____2538 ->
                                 match uu____2538 with
                                 | (t4, uu____2544) -> mk_embedding env t4)
                              args in
                          embed_type_app fv1 arg_embeddings
                      | uu____2545 ->
                          let uu____2546 =
                            let uu____2547 =
                              let uu____2548 =
                                FStar_Syntax_Print.term_to_string t3 in
                              Prims.strcat "Embedding not defined for type "
                                uu____2548 in
                            NoTacticEmbedding uu____2547 in
                          FStar_Exn.raise uu____2546)) in
          let abstract_tvars tvar_names body =
            match tvar_names with
            | [] -> body
            | uu____2560 ->
                let args_tail =
                  FStar_Extraction_ML_Syntax.MLP_Var "args_tail" in
                let mk_cons hd_pat tail_pat =
                  FStar_Extraction_ML_Syntax.MLP_CTor
                    ((["Prims"], "Cons"), [hd_pat; tail_pat]) in
                let fst_pat v1 =
                  FStar_Extraction_ML_Syntax.MLP_Tuple
                    [FStar_Extraction_ML_Syntax.MLP_Var v1;
                    FStar_Extraction_ML_Syntax.MLP_Wild] in
                let pattern =
                  FStar_List.fold_right
                    (fun hd_var -> mk_cons (fst_pat hd_var)) tvar_names
                    args_tail in
                let branch1 =
                  let uu____2597 =
                    let uu____2598 =
                      let uu____2599 =
                        let uu____2606 =
                          let uu____2609 = str_to_name "args_tail" in
                          [uu____2609] in
                        (body, uu____2606) in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2599 in
                    FStar_All.pipe_left w uu____2598 in
                  (pattern, FStar_Pervasives_Native.None, uu____2597) in
                let default_branch =
                  let uu____2623 =
                    let uu____2624 =
                      let uu____2625 =
                        let uu____2632 = str_to_name "failwith" in
                        let uu____2633 =
                          let uu____2636 =
                            let uu____2637 =
                              mlexpr_of_const FStar_Range.dummyRange
                                (FStar_Const.Const_string
                                   ("arity mismatch", FStar_Range.dummyRange)) in
                            FStar_All.pipe_left w uu____2637 in
                          [uu____2636] in
                        (uu____2632, uu____2633) in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2625 in
                    FStar_All.pipe_left w uu____2624 in
                  (FStar_Extraction_ML_Syntax.MLP_Wild,
                    FStar_Pervasives_Native.None, uu____2623) in
                let body1 =
                  let uu____2643 =
                    let uu____2644 =
                      let uu____2659 = str_to_name "args" in
                      (uu____2659, [branch1; default_branch]) in
                    FStar_Extraction_ML_Syntax.MLE_Match uu____2644 in
                  FStar_All.pipe_left w uu____2643 in
                mk_lam "args" body1 in
          let uu____2694 = FStar_Syntax_Util.arrow_formals_comp t1 in
          match uu____2694 with
          | (bs, c) ->
              let result_typ = FStar_Syntax_Util.comp_result c in
              let arity = FStar_List.length bs in
              let uu____2735 =
                let uu____2752 =
                  FStar_Util.prefix_until
                    (fun uu____2786 ->
                       match uu____2786 with
                       | (b, uu____2792) ->
                           let uu____2793 =
                             let uu____2794 =
                               FStar_Syntax_Subst.compress
                                 b.FStar_Syntax_Syntax.sort in
                             uu____2794.FStar_Syntax_Syntax.n in
                           (match uu____2793 with
                            | FStar_Syntax_Syntax.Tm_type uu____2797 -> false
                            | uu____2798 -> true)) bs in
                match uu____2752 with
                | FStar_Pervasives_Native.None -> (bs, [])
                | FStar_Pervasives_Native.Some (tvars, x, rest) ->
                    (tvars, (x :: rest)) in
              (match uu____2735 with
               | (type_vars, bs1) ->
                   let non_tvar_arity = FStar_List.length bs1 in
                   let tvar_names =
                     FStar_List.mapi
                       (fun i ->
                          fun tv ->
                            let uu____2981 = FStar_Util.string_of_int i in
                            Prims.strcat "tv_" uu____2981) type_vars in
                   let tvar_context =
                     FStar_List.map2
                       (fun b ->
                          fun nm ->
                            let uu____3006 = id_embedding nm in
                            ((FStar_Pervasives_Native.fst b), uu____3006))
                       type_vars tvar_names in
                   let rec aux accum_embeddings env bs2 =
                     match bs2 with
                     | [] ->
                         let arg_unembeddings =
                           FStar_All.pipe_right
                             (FStar_List.rev accum_embeddings)
                             (FStar_List.map (fun x -> x.unembed)) in
                         let res_embedding = mk_embedding env result_typ in
                         let uu____3075 = FStar_Syntax_Util.is_pure_comp c in
                         if uu____3075
                         then
                           let embed_fun_N =
                             let uu____3085 =
                               let uu____3086 =
                                 FStar_Util.string_of_int non_tvar_arity in
                               Prims.strcat "arrow_" uu____3086 in
                             mk_basic_embedding Embed S uu____3085 in
                           let args =
                             let uu____3096 =
                               let uu____3099 =
                                 let uu____3102 = lid_to_top_name fv in
                                 [uu____3102] in
                               (res_embedding.embed) :: uu____3099 in
                             FStar_List.append arg_unembeddings uu____3096 in
                           let fun_embedding =
                             FStar_All.pipe_left w
                               (FStar_Extraction_ML_Syntax.MLE_App
                                  (embed_fun_N, args)) in
                           let tabs = abstract_tvars tvar_names fun_embedding in
                           let uu____3107 =
                             let uu____3114 = mk_lam "_psc" tabs in
                             (uu____3114, arity, true) in
                           FStar_Pervasives_Native.Some uu____3107
                         else
                           (let uu____3126 =
                              let uu____3127 =
                                FStar_TypeChecker_Env.norm_eff_name tcenv
                                  (FStar_Syntax_Util.comp_effect_name c) in
                              FStar_Ident.lid_equals uu____3127
                                FStar_Parser_Const.effect_TAC_lid in
                            if uu____3126
                            then
                              let h =
                                let uu____3137 =
                                  let uu____3138 =
                                    FStar_Util.string_of_int arity in
                                  Prims.strcat
                                    "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                                    uu____3138 in
                                str_to_top_name uu____3137 in
                              let tac_fun =
                                let uu____3146 =
                                  let uu____3147 =
                                    let uu____3154 =
                                      let uu____3155 =
                                        let uu____3156 =
                                          FStar_Util.string_of_int arity in
                                        Prims.strcat
                                          "FStar_Tactics_Native.from_tactic_"
                                          uu____3156 in
                                      str_to_top_name uu____3155 in
                                    let uu____3163 =
                                      let uu____3166 = lid_to_top_name fv in
                                      [uu____3166] in
                                    (uu____3154, uu____3163) in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3147 in
                                FStar_All.pipe_left w uu____3146 in
                              let tac_lid_app =
                                let uu____3170 =
                                  let uu____3171 =
                                    let uu____3178 =
                                      str_to_top_name
                                        "FStar_Ident.lid_of_str" in
                                    (uu____3178, [w ml_fv]) in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3171 in
                                FStar_All.pipe_left w uu____3170 in
                              let psc = str_to_name "psc" in
                              let all_args = str_to_name "args" in
                              let args =
                                let uu____3186 =
                                  let uu____3189 =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_Bool
                                            true)) in
                                  [uu____3189; tac_fun] in
                                FStar_List.append uu____3186
                                  (FStar_List.append arg_unembeddings
                                     [res_embedding.embed;
                                     res_embedding.type_repr;
                                     tac_lid_app;
                                     psc]) in
                              let tabs =
                                match tvar_names with
                                | [] ->
                                    let uu____3191 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h,
                                             (FStar_List.append args
                                                [all_args]))) in
                                    mk_lam "args" uu____3191
                                | uu____3194 ->
                                    let uu____3197 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h, args)) in
                                    abstract_tvars tvar_names uu____3197 in
                              let uu____3200 =
                                let uu____3207 = mk_lam "psc" tabs in
                                (uu____3207, (arity + (Prims.parse_int "1")),
                                  false) in
                              FStar_Pervasives_Native.Some uu____3200
                            else
                              (let uu____3221 =
                                 let uu____3222 =
                                   let uu____3223 =
                                     FStar_Syntax_Print.term_to_string t1 in
                                   Prims.strcat
                                     "Plugins not defined for type "
                                     uu____3223 in
                                 NoTacticEmbedding uu____3222 in
                               FStar_Exn.raise uu____3221))
                     | (b, uu____3233)::bs3 ->
                         let uu____3245 =
                           let uu____3248 =
                             mk_embedding env b.FStar_Syntax_Syntax.sort in
                           uu____3248 :: accum_embeddings in
                         aux uu____3245 env bs3 in
                   (try aux [] tvar_context bs1
                    with
                    | NoTacticEmbedding msg ->
                        ((let uu____3281 = FStar_Ident.string_of_lid fv in
                          not_implemented_warning t1.FStar_Syntax_Syntax.pos
                            uu____3281 msg);
                         FStar_Pervasives_Native.None)))