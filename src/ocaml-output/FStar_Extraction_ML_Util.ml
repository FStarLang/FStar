open Prims
let pruneNones:
  'a . 'a FStar_Pervasives_Native.option Prims.list -> 'a Prims.list =
  fun l  ->
    FStar_List.fold_right
      (fun x  ->
         fun ll  ->
           match x with
           | FStar_Pervasives_Native.Some xs -> xs :: ll
           | FStar_Pervasives_Native.None  -> ll) l []
let mk_range_mle: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "mk_range"))
let mlconst_of_const':
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant =
  fun sctt  ->
    match sctt with
    | FStar_Const.Const_effect  -> failwith "Unsupported constant"
    | FStar_Const.Const_range uu____42 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____67) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____73) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____74 ->
        failwith "Unhandled constant: reify/reflect"
let mlconst_of_const:
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const' c
      with
      | uu____89 ->
          let uu____90 =
            let uu____91 = FStar_Range.string_of_range p in
            let uu____92 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____91 uu____92 in
          failwith uu____90
let mlexpr_of_range: FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun r  ->
    let cint i =
      let uu____101 =
        let uu____102 =
          let uu____103 =
            let uu____114 = FStar_Util.string_of_int i in
            (uu____114, FStar_Pervasives_Native.None) in
          FStar_Extraction_ML_Syntax.MLC_Int uu____103 in
        FStar_All.pipe_right uu____102
          (fun _0_41  -> FStar_Extraction_ML_Syntax.MLE_Const _0_41) in
      FStar_All.pipe_right uu____101
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty) in
    let cstr s =
      let uu____129 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_42  -> FStar_Extraction_ML_Syntax.MLE_Const _0_42) in
      FStar_All.pipe_right uu____129
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty) in
    let uu____130 =
      let uu____137 =
        let uu____140 =
          let uu____141 = FStar_Range.file_of_range r in
          FStar_All.pipe_right uu____141 cstr in
        let uu____142 =
          let uu____145 =
            let uu____146 =
              let uu____147 = FStar_Range.start_of_range r in
              FStar_All.pipe_right uu____147 FStar_Range.line_of_pos in
            FStar_All.pipe_right uu____146 cint in
          let uu____148 =
            let uu____151 =
              let uu____152 =
                let uu____153 = FStar_Range.start_of_range r in
                FStar_All.pipe_right uu____153 FStar_Range.col_of_pos in
              FStar_All.pipe_right uu____152 cint in
            let uu____154 =
              let uu____157 =
                let uu____158 =
                  let uu____159 = FStar_Range.end_of_range r in
                  FStar_All.pipe_right uu____159 FStar_Range.line_of_pos in
                FStar_All.pipe_right uu____158 cint in
              let uu____160 =
                let uu____163 =
                  let uu____164 =
                    let uu____165 = FStar_Range.end_of_range r in
                    FStar_All.pipe_right uu____165 FStar_Range.col_of_pos in
                  FStar_All.pipe_right uu____164 cint in
                [uu____163] in
              uu____157 :: uu____160 in
            uu____151 :: uu____154 in
          uu____145 :: uu____148 in
        uu____140 :: uu____142 in
      (mk_range_mle, uu____137) in
    FStar_Extraction_ML_Syntax.MLE_App uu____130
let mlexpr_of_const:
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____177 ->
          let uu____178 = mlconst_of_const p c in
          FStar_Extraction_ML_Syntax.MLE_Const uu____178
let rec subst_aux:
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____200 =
            FStar_Util.find_opt
              (fun uu____214  ->
                 match uu____214 with | (y,uu____220) -> y = x) subst1 in
          (match uu____200 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____237 =
            let uu____244 = subst_aux subst1 t1 in
            let uu____245 = subst_aux subst1 t2 in (uu____244, f, uu____245) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____237
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____252 =
            let uu____259 = FStar_List.map (subst_aux subst1) args in
            (uu____259, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____252
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____267 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____267
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let try_subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun uu____280  ->
    fun args  ->
      match uu____280 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____291 =
               let uu____292 = FStar_List.zip formals args in
               subst_aux uu____292 t in
             FStar_Pervasives_Native.Some uu____291)
let subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun ts  ->
    fun args  ->
      let uu____311 = try_subst ts args in
      match uu____311 with
      | FStar_Pervasives_Native.None  ->
          failwith
            "Substitution must be fully applied (see GitHub issue #490)"
      | FStar_Pervasives_Native.Some t -> t
let udelta_unfold:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun g  ->
    fun uu___147_324  ->
      match uu___147_324 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____333 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____333 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____339 = try_subst ts args in
               (match uu____339 with
                | FStar_Pervasives_Native.None  ->
                    let uu____344 =
                      let uu____345 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1 in
                      let uu____346 =
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu____347 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____345 uu____346 uu____347 in
                    failwith uu____344
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____351 -> FStar_Pervasives_Native.None)
      | uu____354 -> FStar_Pervasives_Native.None
let eff_leq:
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____363) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____364 -> false
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___148_372  ->
    match uu___148_372 with
    | FStar_Extraction_ML_Syntax.E_PURE  -> "Pure"
    | FStar_Extraction_ML_Syntax.E_GHOST  -> "Ghost"
    | FStar_Extraction_ML_Syntax.E_IMPURE  -> "Impure"
let join:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.e_tag -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun f  ->
      fun f'  ->
        match (f, f') with
        | (FStar_Extraction_ML_Syntax.E_IMPURE
           ,FStar_Extraction_ML_Syntax.E_PURE ) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.E_IMPURE ) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_IMPURE
           ,FStar_Extraction_ML_Syntax.E_IMPURE ) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_GHOST
           ,FStar_Extraction_ML_Syntax.E_GHOST ) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.E_GHOST ) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_GHOST
           ,FStar_Extraction_ML_Syntax.E_PURE ) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.E_PURE ) ->
            FStar_Extraction_ML_Syntax.E_PURE
        | uu____385 ->
            let uu____390 =
              let uu____391 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____391
                (eff_to_string f) (eff_to_string f') in
            failwith uu____390
let join_l:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun:
  'Auu____410 .
    Prims.unit ->
      ('Auu____410,FStar_Extraction_ML_Syntax.mlty)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____421  ->
    FStar_List.fold_right
      (fun uu____430  ->
         fun t  ->
           match uu____430 with
           | (uu____436,t0) ->
               FStar_Extraction_ML_Syntax.MLTY_Fun
                 (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option[@@deriving
                                                                    show]
let rec type_leq_c:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2
  =
  fun unfold_ty  ->
    fun e  ->
      fun t  ->
        fun t'  ->
          match (t, t') with
          | (FStar_Extraction_ML_Syntax.MLTY_Var
             x,FStar_Extraction_ML_Syntax.MLTY_Var y) ->
              if x = y
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Fun
             (t1,f,t2),FStar_Extraction_ML_Syntax.MLTY_Fun (t1',f',t2')) ->
              let mk_fun xs body =
                match xs with
                | [] -> body
                | uu____523 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____555 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____562 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____562 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____572;
                     FStar_Extraction_ML_Syntax.loc = uu____573;_}
                   ->
                   let uu____594 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____594
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____610 = type_leq unfold_ty t2 t2' in
                        (if uu____610
                         then
                           let body1 =
                             let uu____621 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____621
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____626 =
                             let uu____629 =
                               let uu____630 =
                                 let uu____633 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____633 in
                               FStar_All.pipe_left uu____630
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu____629 in
                           (true, uu____626)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____662 =
                           let uu____669 =
                             let uu____672 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun _0_43  ->
                                  FStar_Pervasives_Native.Some _0_43)
                               uu____672 in
                           type_leq_c unfold_ty uu____669 t2 t2' in
                         match uu____662 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____696 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu____696
                               | uu____705 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____713 ->
                   let uu____716 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____716
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____752 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____752
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____768 = unfold_ty t in
                 match uu____768 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____782 = unfold_ty t' in
                     (match uu____782 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____804 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____804
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____821,uu____822) ->
              let uu____829 = unfold_ty t in
              (match uu____829 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____843 -> (false, FStar_Pervasives_Native.None))
          | (uu____848,FStar_Extraction_ML_Syntax.MLTY_Named uu____849) ->
              let uu____856 = unfold_ty t' in
              (match uu____856 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____870 -> (false, FStar_Pervasives_Native.None))
          | uu____875 -> (false, FStar_Pervasives_Native.None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____886 = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_All.pipe_right uu____886 FStar_Pervasives_Native.fst
let is_type_abstraction:
  'Auu____912 'Auu____913 'Auu____914 .
    (('Auu____914,'Auu____913) FStar_Util.either,'Auu____912)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun uu___149_928  ->
    match uu___149_928 with
    | (FStar_Util.Inl uu____939,uu____940)::uu____941 -> true
    | uu____964 -> false
let is_xtuple:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____986  ->
    match uu____986 with
    | (ns,n1) ->
        let uu____1001 =
          let uu____1002 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_datacon_string uu____1002 in
        if uu____1001
        then
          let uu____1005 =
            let uu____1006 = FStar_Util.char_at n1 (Prims.parse_int "7") in
            FStar_Util.int_of_char uu____1006 in
          FStar_Pervasives_Native.Some uu____1005
        else FStar_Pervasives_Native.None
let resugar_exp:
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1018 = is_xtuple mlp in
        (match uu____1018 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1022 -> e)
    | uu____1025 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___150_1033  ->
    match uu___150_1033 with
    | f::uu____1039 ->
        let uu____1042 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____1042 with
         | (ns,uu____1052) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____1063 -> failwith "impos"
let record_fields:
  'Auu____1074 .
    FStar_Ident.lident Prims.list ->
      'Auu____1074 Prims.list ->
        (Prims.string,'Auu____1074) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2
        (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e))
        fs vs
let is_xtuple_ty:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____1116  ->
    match uu____1116 with
    | (ns,n1) ->
        let uu____1131 =
          let uu____1132 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_constructor_string uu____1132 in
        if uu____1131
        then
          let uu____1135 =
            let uu____1136 = FStar_Util.char_at n1 (Prims.parse_int "5") in
            FStar_Util.int_of_char uu____1136 in
          FStar_Pervasives_Native.Some uu____1135
        else FStar_Pervasives_Native.None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1148 = is_xtuple_ty mlp in
        (match uu____1148 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1152 -> t)
    | uu____1155 -> t
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____1164 = FStar_Options.codegen_fsharp () in
    if uu____1164
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string
  =
  fun uu____1175  ->
    match uu____1175 with
    | (ns,n1) ->
        let uu____1188 = FStar_Options.codegen_fsharp () in
        if uu____1188
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____1200 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____1200, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____1223 = unfold_ty t in
         match uu____1223 with
         | FStar_Pervasives_Native.Some t1 -> erasableType unfold_ty t1
         | FStar_Pervasives_Native.None  -> false)
let rec eraseTypeDeep:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun unfold_ty  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Fun (tyd,etag,tycd) ->
          if etag = FStar_Extraction_ML_Syntax.E_PURE
          then
            let uu____1245 =
              let uu____1252 = eraseTypeDeep unfold_ty tyd in
              let uu____1256 = eraseTypeDeep unfold_ty tycd in
              (uu____1252, etag, uu____1256) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1245
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1267 = erasableType unfold_ty t in
          if uu____1267
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1272 =
               let uu____1279 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____1279, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1272)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1290 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1290
      | uu____1296 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____1299 =
    let uu____1302 =
      (mk_ty_fun ())
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____1302 in
  FStar_All.pipe_left uu____1299
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_AmpAmp"))
let conjoin:
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun e1  ->
    fun e2  ->
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_bool_ty)
        (FStar_Extraction_ML_Syntax.MLE_App (prims_op_amp_amp, [e1; e2]))
let conjoin_opt:
  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option
  =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.None
      | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.Some x
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some x) ->
          FStar_Pervasives_Native.Some x
      | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
          let uu____1371 = conjoin x y in
          FStar_Pervasives_Native.Some uu____1371
let mlloc_of_range:
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____1382 = FStar_Range.file_of_range r in (line, uu____1382)
let rec doms_and_cod:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1400,b) ->
        let uu____1402 = doms_and_cod b in
        (match uu____1402 with | (ds,c) -> ((a :: ds), c))
    | uu____1423 -> ([], t)
let argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    let uu____1434 = doms_and_cod t in FStar_Pervasives_Native.fst uu____1434
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1460,b) ->
        let uu____1462 = uncurry_mlty_fun b in
        (match uu____1462 with | (args,res) -> ((a :: args), res))
    | uu____1483 -> ([], t)
exception CallNotImplemented
let uu___is_CallNotImplemented: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | CallNotImplemented  -> true | uu____1490 -> false
let not_implemented_warning: Prims.string -> Prims.unit =
  fun t  ->
    FStar_Util.print1_warning ". Tactic %s will not run natively.\n" t
type emb_decl =
  | Embed
  | Unembed[@@deriving show]
let uu___is_Embed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____1499 -> false
let uu___is_Unembed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____1504 -> false
let lid_to_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun l  ->
    let uu____1509 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
    FStar_Extraction_ML_Syntax.MLE_Name uu____1509
let lid_to_top_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun l  ->
    let uu____1514 =
      let uu____1515 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
      FStar_Extraction_ML_Syntax.MLE_Name uu____1515 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1514
let str_to_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  ->
    let uu____1520 = FStar_Ident.lid_of_str s in lid_to_name uu____1520
let str_to_top_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr =
  fun s  ->
    let uu____1525 = FStar_Ident.lid_of_str s in lid_to_top_name uu____1525
let fstar_syn_syn_prefix: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr'
  = fun s  -> str_to_name (Prims.strcat "FStar_Syntax_Syntax." s)
let fstar_tc_common_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_TypeChecker_Common." s)
let fstar_refl_basic_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Basic." s)
let fstar_refl_data_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Data." s)
let fstar_emb_basic_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)
let mk_basic_embedding:
  emb_decl -> Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun m  ->
    fun s  ->
      match m with
      | Embed  -> fstar_emb_basic_prefix (Prims.strcat "embed_" s)
      | Unembed  -> fstar_emb_basic_prefix (Prims.strcat "unembed_" s)
let mk_embedding:
  emb_decl -> Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun m  ->
    fun s  ->
      match m with
      | Embed  -> fstar_refl_basic_prefix (Prims.strcat "embed_" s)
      | Unembed  -> fstar_refl_basic_prefix (Prims.strcat "unembed_" s)
let mk_tactic_unembedding:
  FStar_Extraction_ML_Syntax.mlexpr' Prims.list ->
    FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun args  ->
    let tac_arg = "t" in
    let reify_tactic =
      let uu____1572 =
        let uu____1573 =
          let uu____1580 =
            str_to_top_name "FStar_Tactics_Interpreter.reify_tactic" in
          let uu____1581 =
            let uu____1584 = str_to_top_name tac_arg in [uu____1584] in
          (uu____1580, uu____1581) in
        FStar_Extraction_ML_Syntax.MLE_App uu____1573 in
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1572 in
    let from_tac =
      let uu____1588 =
        let uu____1589 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Builtins.from_tac_" uu____1589 in
      str_to_top_name uu____1588 in
    let unembed_tactic =
      let uu____1591 =
        let uu____1592 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Interpreter.unembed_tactic_" uu____1592 in
      str_to_top_name uu____1591 in
    let app =
      match FStar_List.length args with
      | _0_44 when _0_44 = (Prims.parse_int "1") ->
          let uu____1594 =
            let uu____1601 =
              let uu____1604 =
                let uu____1605 =
                  let uu____1606 =
                    let uu____1613 =
                      let uu____1616 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) args in
                      FStar_List.append uu____1616 [reify_tactic] in
                    (unembed_tactic, uu____1613) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1606 in
                FStar_Extraction_ML_Syntax.with_ty
                  FStar_Extraction_ML_Syntax.MLTY_Top uu____1605 in
              [uu____1604] in
            (from_tac, uu____1601) in
          FStar_Extraction_ML_Syntax.MLE_App uu____1594
      | n1 ->
          ((let uu____1625 = FStar_Util.string_of_int n1 in
            FStar_Util.print1_warning
              "Unembedding not defined for tactics of %s arguments\n"
              uu____1625);
           FStar_Exn.raise CallNotImplemented) in
    FStar_Extraction_ML_Syntax.MLE_Fun
      ([(tac_arg, FStar_Extraction_ML_Syntax.MLTY_Top);
       ("()", FStar_Extraction_ML_Syntax.MLTY_Top)],
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top app))
let rec mk_tac_param_type:
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun t  ->
    let uu____1654 =
      let uu____1655 = FStar_Syntax_Subst.compress t in
      uu____1655.FStar_Syntax_Syntax.n in
    match uu____1654 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
        fstar_syn_syn_prefix "t_int"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
        fstar_syn_syn_prefix "t_bool"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
        fstar_syn_syn_prefix "t_unit"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid ->
        fstar_syn_syn_prefix "t_string"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1663 = FStar_Reflection_Data.fstar_refl_types_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1663 ->
        fstar_refl_data_prefix "t_binder"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1665 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1665 ->
        fstar_refl_data_prefix "t_term"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1667 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1667 ->
        fstar_refl_data_prefix "t_fv"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1669 = FStar_Reflection_Data.fstar_refl_syntax_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1669 ->
        fstar_refl_data_prefix "t_binders"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1671 =
          FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1671 ->
        fstar_refl_data_prefix "t_norm_step"
    | FStar_Syntax_Syntax.Tm_app (h,args) ->
        let uu____1694 =
          let uu____1695 = FStar_Syntax_Subst.compress h in
          uu____1695.FStar_Syntax_Syntax.n in
        (match uu____1694 with
         | FStar_Syntax_Syntax.Tm_uinst (h',uu____1699) ->
             let uu____1704 =
               let uu____1705 = FStar_Syntax_Subst.compress h' in
               uu____1705.FStar_Syntax_Syntax.n in
             (match uu____1704 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.list_lid
                  ->
                  let arg_term =
                    let uu____1712 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1712 in
                  let uu____1727 =
                    let uu____1734 =
                      let uu____1735 = fstar_tc_common_prefix "t_list_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1735 in
                    let uu____1736 =
                      let uu____1739 =
                        let uu____1742 = mk_tac_param_type arg_term in
                        [uu____1742] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1739 in
                    (uu____1734, uu____1736) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1727
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.option_lid
                  ->
                  let arg_term =
                    let uu____1749 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1749 in
                  let uu____1764 =
                    let uu____1771 =
                      let uu____1772 = fstar_tc_common_prefix "t_option_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1772 in
                    let uu____1773 =
                      let uu____1776 =
                        let uu____1779 = mk_tac_param_type arg_term in
                        [uu____1779] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1776 in
                    (uu____1771, uu____1773) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1764
              | uu____1782 ->
                  ((let uu____1784 =
                      let uu____1785 =
                        let uu____1786 = FStar_Syntax_Subst.compress h' in
                        FStar_Syntax_Print.term_to_string uu____1786 in
                      Prims.strcat
                        "Type term not defined for higher-order type "
                        uu____1785 in
                    FStar_Util.print_warning uu____1784);
                   FStar_Exn.raise CallNotImplemented))
         | uu____1787 ->
             (FStar_Util.print_warning "Impossible\n";
              FStar_Exn.raise CallNotImplemented))
    | uu____1789 ->
        ((let uu____1791 =
            let uu____1792 =
              let uu____1793 = FStar_Syntax_Subst.compress t in
              FStar_Syntax_Print.term_to_string uu____1793 in
            Prims.strcat "Type term not defined for " uu____1792 in
          FStar_Util.print_warning uu____1791);
         FStar_Exn.raise CallNotImplemented)
let rec mk_tac_embedding_path:
  emb_decl -> FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun m  ->
    fun t  ->
      let uu____1802 =
        let uu____1803 = FStar_Syntax_Subst.compress t in
        uu____1803.FStar_Syntax_Syntax.n in
      match uu____1802 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
          mk_basic_embedding m "int"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
          mk_basic_embedding m "bool"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
          mk_basic_embedding m "unit"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid ->
          mk_basic_embedding m "string"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1811 =
            FStar_Reflection_Data.fstar_refl_types_lid "binder" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1811 ->
          mk_embedding m "binder"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1813 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1813 ->
          mk_embedding m "term"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1815 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1815 ->
          mk_embedding m "fvar"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1817 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "binders" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1817 ->
          mk_embedding m "binders"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1819 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1819 ->
          mk_embedding m "norm_step"
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____1842 =
            let uu____1843 = FStar_Syntax_Subst.compress h in
            uu____1843.FStar_Syntax_Syntax.n in
          (match uu____1842 with
           | FStar_Syntax_Syntax.Tm_uinst (h',uu____1847) ->
               let uu____1852 =
                 let uu____1863 =
                   let uu____1864 = FStar_Syntax_Subst.compress h' in
                   uu____1864.FStar_Syntax_Syntax.n in
                 match uu____1863 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.list_lid
                     ->
                     let arg_term =
                       let uu____1881 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1881 in
                     let uu____1896 =
                       let uu____1899 = mk_tac_embedding_path m arg_term in
                       [uu____1899] in
                     let uu____1900 = mk_tac_param_type arg_term in
                     ("list", uu____1896, uu____1900, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.option_lid
                     ->
                     let arg_term =
                       let uu____1907 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1907 in
                     let uu____1922 =
                       let uu____1925 = mk_tac_embedding_path m arg_term in
                       [uu____1925] in
                     let uu____1926 = mk_tac_param_type arg_term in
                     ("option", uu____1922, uu____1926, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.tactic_lid
                     ->
                     let arg_term =
                       let uu____1933 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1933 in
                     let uu____1948 =
                       let uu____1951 = mk_tac_embedding_path m arg_term in
                       [uu____1951] in
                     let uu____1952 = mk_tac_param_type arg_term in
                     ("list", uu____1948, uu____1952, true)
                 | uu____1955 ->
                     ((let uu____1957 =
                         let uu____1958 =
                           let uu____1959 = FStar_Syntax_Subst.compress h' in
                           FStar_Syntax_Print.term_to_string uu____1959 in
                         Prims.strcat
                           "Embedding not defined for higher-order type "
                           uu____1958 in
                       FStar_Util.print_warning uu____1957);
                      FStar_Exn.raise CallNotImplemented) in
               (match uu____1852 with
                | (ht,hargs,type_arg,is_tactic) ->
                    let hargs1 =
                      match m with
                      | Embed  -> FStar_List.append hargs [type_arg]
                      | Unembed  -> hargs in
                    if is_tactic
                    then
                      (match m with
                       | Embed  ->
                           (FStar_Util.print_warning
                              "Embedding not defined for tactic type\n";
                            FStar_Exn.raise CallNotImplemented)
                       | Unembed  -> mk_tactic_unembedding hargs1)
                    else
                      (let uu____1985 =
                         let uu____1992 =
                           let uu____1993 = mk_basic_embedding m ht in
                           FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top uu____1993 in
                         let uu____1994 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top) hargs1 in
                         (uu____1992, uu____1994) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____1985))
           | uu____1999 ->
               (FStar_Util.print_warning "Impossible\n";
                FStar_Exn.raise CallNotImplemented))
      | uu____2001 ->
          ((let uu____2003 =
              let uu____2004 =
                let uu____2005 = FStar_Syntax_Subst.compress t in
                FStar_Syntax_Print.term_to_string uu____2005 in
              Prims.strcat "Embedding not defined for type " uu____2004 in
            FStar_Util.print_warning uu____2003);
           FStar_Exn.raise CallNotImplemented)
let mk_interpretation_fun:
  'Auu____2016 .
    FStar_Ident.lident ->
      FStar_Extraction_ML_Syntax.mlexpr' ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,'Auu____2016)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Extraction_ML_Syntax.mlexpr' FStar_Pervasives_Native.option
  =
  fun tac_lid  ->
    fun assm_lid  ->
      fun t  ->
        fun bs  ->
          try
            let arg_types =
              FStar_List.map
                (fun x  ->
                   (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
                bs in
            let arity = FStar_List.length bs in
            let h =
              let uu____2084 =
                let uu____2085 = FStar_Util.string_of_int arity in
                Prims.strcat
                  "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                  uu____2085 in
              str_to_top_name uu____2084 in
            let tac_fun =
              let uu____2093 =
                let uu____2100 =
                  let uu____2101 =
                    let uu____2102 = FStar_Util.string_of_int arity in
                    Prims.strcat "FStar_Tactics_Native.from_tactic_"
                      uu____2102 in
                  str_to_top_name uu____2101 in
                let uu____2109 =
                  let uu____2112 = lid_to_top_name tac_lid in [uu____2112] in
                (uu____2100, uu____2109) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2093 in
            let tac_lid_app =
              let uu____2116 =
                let uu____2123 = str_to_top_name "FStar_Ident.lid_of_str" in
                (uu____2123,
                  [FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.MLTY_Top assm_lid]) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2116 in
            let psc = str_to_name "psc" in
            let args =
              let uu____2130 =
                let uu____2133 =
                  FStar_List.map (mk_tac_embedding_path Unembed) arg_types in
                let uu____2136 =
                  let uu____2139 = mk_tac_embedding_path Embed t in
                  let uu____2140 =
                    let uu____2143 = mk_tac_param_type t in
                    let uu____2144 =
                      let uu____2147 =
                        let uu____2150 =
                          let uu____2153 = str_to_name "args" in [uu____2153] in
                        psc :: uu____2150 in
                      tac_lid_app :: uu____2147 in
                    uu____2143 :: uu____2144 in
                  uu____2139 :: uu____2140 in
                FStar_List.append uu____2133 uu____2136 in
              FStar_List.append [tac_fun] uu____2130 in
            let app =
              let uu____2155 =
                let uu____2156 =
                  let uu____2163 =
                    FStar_List.map
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top) args in
                  (h, uu____2163) in
                FStar_Extraction_ML_Syntax.MLE_App uu____2156 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2155 in
            FStar_Pervasives_Native.Some
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([("psc", FStar_Extraction_ML_Syntax.MLTY_Top);
                  ("args", FStar_Extraction_ML_Syntax.MLTY_Top)], app))
          with
          | CallNotImplemented  ->
              ((let uu____2192 = FStar_Ident.string_of_lid tac_lid in
                not_implemented_warning uu____2192);
               FStar_Pervasives_Native.None)