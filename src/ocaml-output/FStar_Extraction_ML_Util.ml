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
    | FStar_Const.Const_range uu____39 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____73) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____79) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____80 ->
        failwith "Unhandled constant: reify/reflect"
let mlconst_of_const:
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const' c
      with
      | uu____93 ->
          let uu____94 =
            let uu____95 = FStar_Range.string_of_range p in
            let uu____96 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____95 uu____96 in
          failwith uu____94
let mlexpr_of_range: FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun r  ->
    let cint i =
      let uu____104 =
        let uu____105 =
          let uu____106 =
            let uu____117 = FStar_Util.string_of_int i in
            (uu____117, FStar_Pervasives_Native.None) in
          FStar_Extraction_ML_Syntax.MLC_Int uu____106 in
        FStar_All.pipe_right uu____105
          (fun _0_41  -> FStar_Extraction_ML_Syntax.MLE_Const _0_41) in
      FStar_All.pipe_right uu____104
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty) in
    let cstr s =
      let uu____132 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_42  -> FStar_Extraction_ML_Syntax.MLE_Const _0_42) in
      FStar_All.pipe_right uu____132
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty) in
    let uu____133 =
      let uu____140 =
        let uu____143 =
          let uu____144 = FStar_Range.file_of_range r in
          FStar_All.pipe_right uu____144 cstr in
        let uu____145 =
          let uu____148 =
            let uu____149 =
              let uu____150 = FStar_Range.start_of_range r in
              FStar_All.pipe_right uu____150 FStar_Range.line_of_pos in
            FStar_All.pipe_right uu____149 cint in
          let uu____151 =
            let uu____154 =
              let uu____155 =
                let uu____156 = FStar_Range.start_of_range r in
                FStar_All.pipe_right uu____156 FStar_Range.col_of_pos in
              FStar_All.pipe_right uu____155 cint in
            let uu____157 =
              let uu____160 =
                let uu____161 =
                  let uu____162 = FStar_Range.end_of_range r in
                  FStar_All.pipe_right uu____162 FStar_Range.line_of_pos in
                FStar_All.pipe_right uu____161 cint in
              let uu____163 =
                let uu____166 =
                  let uu____167 =
                    let uu____168 = FStar_Range.end_of_range r in
                    FStar_All.pipe_right uu____168 FStar_Range.col_of_pos in
                  FStar_All.pipe_right uu____167 cint in
                [uu____166] in
              uu____160 :: uu____163 in
            uu____154 :: uu____157 in
          uu____148 :: uu____151 in
        uu____143 :: uu____145 in
      (mk_range_mle, uu____140) in
    FStar_Extraction_ML_Syntax.MLE_App uu____133
let mlexpr_of_const:
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____178 ->
          let uu____179 = mlconst_of_const p c in
          FStar_Extraction_ML_Syntax.MLE_Const uu____179
let rec subst_aux:
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____199 =
            FStar_Util.find_opt
              (fun uu____213  ->
                 match uu____213 with | (y,uu____219) -> y = x) subst1 in
          (match uu____199 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____236 =
            let uu____243 = subst_aux subst1 t1 in
            let uu____244 = subst_aux subst1 t2 in (uu____243, f, uu____244) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____236
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____251 =
            let uu____258 = FStar_List.map (subst_aux subst1) args in
            (uu____258, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____251
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____266 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____266
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let try_subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun uu____277  ->
    fun args  ->
      match uu____277 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____288 =
               let uu____289 = FStar_List.zip formals args in
               subst_aux uu____289 t in
             FStar_Pervasives_Native.Some uu____288)
let subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun ts  ->
    fun args  ->
      let uu____306 = try_subst ts args in
      match uu____306 with
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
    fun uu___179_317  ->
      match uu___179_317 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____326 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____326 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____332 = try_subst ts args in
               (match uu____332 with
                | FStar_Pervasives_Native.None  ->
                    let uu____337 =
                      let uu____338 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1 in
                      let uu____339 =
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu____340 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____338 uu____339 uu____340 in
                    failwith uu____337
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____344 -> FStar_Pervasives_Native.None)
      | uu____347 -> FStar_Pervasives_Native.None
let eff_leq:
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____354) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____355 -> false
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___180_362  ->
    match uu___180_362 with
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
        | uu____372 ->
            let uu____377 =
              let uu____378 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____378
                (eff_to_string f) (eff_to_string f') in
            failwith uu____377
let join_l:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun:
  'Auu____392 .
    Prims.unit ->
      ('Auu____392,FStar_Extraction_ML_Syntax.mlty)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____403  ->
    FStar_List.fold_right
      (fun uu____412  ->
         fun t  ->
           match uu____412 with
           | (uu____418,t0) ->
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
                | uu____505 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____537 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____544 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____544 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____554;
                     FStar_Extraction_ML_Syntax.loc = uu____555;_}
                   ->
                   let uu____576 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____576
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____592 = type_leq unfold_ty t2 t2' in
                        (if uu____592
                         then
                           let body1 =
                             let uu____603 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____603
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____608 =
                             let uu____611 =
                               let uu____612 =
                                 let uu____615 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____615 in
                               FStar_All.pipe_left uu____612
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu____611 in
                           (true, uu____608)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____644 =
                           let uu____651 =
                             let uu____654 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun _0_43  ->
                                  FStar_Pervasives_Native.Some _0_43)
                               uu____654 in
                           type_leq_c unfold_ty uu____651 t2 t2' in
                         match uu____644 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____678 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu____678
                               | uu____687 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____695 ->
                   let uu____698 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____698
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____734 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____734
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____750 = unfold_ty t in
                 match uu____750 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____764 = unfold_ty t' in
                     (match uu____764 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____786 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____786
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____803,uu____804) ->
              let uu____811 = unfold_ty t in
              (match uu____811 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____825 -> (false, FStar_Pervasives_Native.None))
          | (uu____830,FStar_Extraction_ML_Syntax.MLTY_Named uu____831) ->
              let uu____838 = unfold_ty t' in
              (match uu____838 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____852 -> (false, FStar_Pervasives_Native.None))
          | uu____857 -> (false, FStar_Pervasives_Native.None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____868 = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_All.pipe_right uu____868 FStar_Pervasives_Native.fst
let is_type_abstraction:
  'Auu____890 'Auu____891 'Auu____892 .
    (('Auu____892,'Auu____891) FStar_Util.either,'Auu____890)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun uu___181_906  ->
    match uu___181_906 with
    | (FStar_Util.Inl uu____917,uu____918)::uu____919 -> true
    | uu____942 -> false
let is_xtuple:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____963  ->
    match uu____963 with
    | (ns,n1) ->
        let uu____978 =
          let uu____979 = FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_datacon_string uu____979 in
        if uu____978
        then
          let uu____982 =
            let uu____983 = FStar_Util.char_at n1 (Prims.parse_int "7") in
            FStar_Util.int_of_char uu____983 in
          FStar_Pervasives_Native.Some uu____982
        else FStar_Pervasives_Native.None
let resugar_exp:
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1003 = is_xtuple mlp in
        (match uu____1003 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1007 -> e)
    | uu____1010 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___182_1017  ->
    match uu___182_1017 with
    | f::uu____1023 ->
        let uu____1026 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____1026 with
         | (ns,uu____1036) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1047 -> failwith "impos"
let record_fields:
  'Auu____1055 .
    FStar_Ident.lident Prims.list ->
      'Auu____1055 Prims.list ->
        (Prims.string,'Auu____1055) FStar_Pervasives_Native.tuple2 Prims.list
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
  fun uu____1096  ->
    match uu____1096 with
    | (ns,n1) ->
        let uu____1111 =
          let uu____1112 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_constructor_string uu____1112 in
        if uu____1111
        then
          let uu____1115 =
            let uu____1116 = FStar_Util.char_at n1 (Prims.parse_int "5") in
            FStar_Util.int_of_char uu____1116 in
          FStar_Pervasives_Native.Some uu____1115
        else FStar_Pervasives_Native.None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1136 = is_xtuple_ty mlp in
        (match uu____1136 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1140 -> t)
    | uu____1143 -> t
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____1151 = FStar_Options.codegen_fsharp () in
    if uu____1151
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string
  =
  fun uu____1161  ->
    match uu____1161 with
    | (ns,n1) ->
        let uu____1174 = FStar_Options.codegen_fsharp () in
        if uu____1174
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____1185 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____1185, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      let uu____1205 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t in
      if uu____1205
      then true
      else
        (let uu____1207 = unfold_ty t in
         match uu____1207 with
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
            let uu____1227 =
              let uu____1234 = eraseTypeDeep unfold_ty tyd in
              let uu____1238 = eraseTypeDeep unfold_ty tycd in
              (uu____1234, etag, uu____1238) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1227
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1249 = erasableType unfold_ty t in
          if uu____1249
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1254 =
               let uu____1261 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____1261, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1254)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1272 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1272
      | uu____1278 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____1281 =
    let uu____1284 =
      (mk_ty_fun ())
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____1284 in
  FStar_All.pipe_left uu____1281
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
          let uu____1349 = conjoin x y in
          FStar_Pervasives_Native.Some uu____1349
let mlloc_of_range:
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____1359 = FStar_Range.file_of_range r in (line, uu____1359)
let rec doms_and_cod:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1376,b) ->
        let uu____1378 = doms_and_cod b in
        (match uu____1378 with | (ds,c) -> ((a :: ds), c))
    | uu____1399 -> ([], t)
let argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    let uu____1409 = doms_and_cod t in FStar_Pervasives_Native.fst uu____1409
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1434,b) ->
        let uu____1436 = uncurry_mlty_fun b in
        (match uu____1436 with | (args,res) -> ((a :: args), res))
    | uu____1457 -> ([], t)
exception CallNotImplemented
let uu___is_CallNotImplemented: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | CallNotImplemented  -> true | uu____1463 -> false
let not_implemented_warning: Prims.string -> Prims.unit =
  fun t  ->
    FStar_Util.print1_warning ". Tactic %s will not run natively.\n" t
type emb_decl =
  | Embed
  | Unembed[@@deriving show]
let uu___is_Embed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____1470 -> false
let uu___is_Unembed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____1474 -> false
let lid_to_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun l  ->
    let uu____1478 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
    FStar_Extraction_ML_Syntax.MLE_Name uu____1478
let lid_to_top_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun l  ->
    let uu____1482 =
      let uu____1483 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
      FStar_Extraction_ML_Syntax.MLE_Name uu____1483 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1482
let str_to_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  ->
    let uu____1487 = FStar_Ident.lid_of_str s in lid_to_name uu____1487
let str_to_top_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr =
  fun s  ->
    let uu____1491 = FStar_Ident.lid_of_str s in lid_to_top_name uu____1491
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
      let uu____1528 =
        let uu____1529 =
          let uu____1536 =
            str_to_top_name "FStar_Tactics_Interpreter.reify_tactic" in
          let uu____1537 =
            let uu____1540 = str_to_top_name tac_arg in [uu____1540] in
          (uu____1536, uu____1537) in
        FStar_Extraction_ML_Syntax.MLE_App uu____1529 in
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1528 in
    let from_tac =
      let uu____1544 =
        let uu____1545 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Builtins.from_tac_" uu____1545 in
      str_to_top_name uu____1544 in
    let unembed_tactic =
      let uu____1547 =
        let uu____1548 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Interpreter.unembed_tactic_" uu____1548 in
      str_to_top_name uu____1547 in
    let app =
      match FStar_List.length args with
      | _0_44 when _0_44 = (Prims.parse_int "1") ->
          let uu____1550 =
            let uu____1557 =
              let uu____1560 =
                let uu____1561 =
                  let uu____1562 =
                    let uu____1569 =
                      let uu____1572 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) args in
                      FStar_List.append uu____1572 [reify_tactic] in
                    (unembed_tactic, uu____1569) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1562 in
                FStar_Extraction_ML_Syntax.with_ty
                  FStar_Extraction_ML_Syntax.MLTY_Top uu____1561 in
              [uu____1560] in
            (from_tac, uu____1557) in
          FStar_Extraction_ML_Syntax.MLE_App uu____1550
      | n1 ->
          ((let uu____1581 = FStar_Util.string_of_int n1 in
            FStar_Util.print1_warning
              "Unembedding not defined for tactics of %s arguments\n"
              uu____1581);
           FStar_Exn.raise CallNotImplemented) in
    FStar_Extraction_ML_Syntax.MLE_Fun
      ([(tac_arg, FStar_Extraction_ML_Syntax.MLTY_Top);
       ("()", FStar_Extraction_ML_Syntax.MLTY_Top)],
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top app))
let rec mk_tac_param_type:
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun t  ->
    let uu____1609 =
      let uu____1610 = FStar_Syntax_Subst.compress t in
      uu____1610.FStar_Syntax_Syntax.n in
    match uu____1609 with
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
        let uu____1618 = FStar_Reflection_Data.fstar_refl_types_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1618 ->
        fstar_refl_data_prefix "t_binder"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1620 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1620 ->
        fstar_refl_data_prefix "t_term"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1622 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1622 ->
        fstar_refl_data_prefix "t_fv"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1624 = FStar_Reflection_Data.fstar_refl_syntax_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1624 ->
        fstar_refl_data_prefix "t_binders"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1626 =
          FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1626 ->
        fstar_refl_data_prefix "t_norm_step"
    | FStar_Syntax_Syntax.Tm_app (h,args) ->
        let uu____1649 =
          let uu____1650 = FStar_Syntax_Subst.compress h in
          uu____1650.FStar_Syntax_Syntax.n in
        (match uu____1649 with
         | FStar_Syntax_Syntax.Tm_uinst (h',uu____1654) ->
             let uu____1659 =
               let uu____1660 = FStar_Syntax_Subst.compress h' in
               uu____1660.FStar_Syntax_Syntax.n in
             (match uu____1659 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.list_lid
                  ->
                  let arg_term =
                    let uu____1667 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1667 in
                  let uu____1682 =
                    let uu____1689 =
                      let uu____1690 = fstar_tc_common_prefix "t_list_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1690 in
                    let uu____1691 =
                      let uu____1694 =
                        let uu____1697 = mk_tac_param_type arg_term in
                        [uu____1697] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1694 in
                    (uu____1689, uu____1691) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1682
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.option_lid
                  ->
                  let arg_term =
                    let uu____1704 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1704 in
                  let uu____1719 =
                    let uu____1726 =
                      let uu____1727 = fstar_tc_common_prefix "t_option_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1727 in
                    let uu____1728 =
                      let uu____1731 =
                        let uu____1734 = mk_tac_param_type arg_term in
                        [uu____1734] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1731 in
                    (uu____1726, uu____1728) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1719
              | uu____1737 ->
                  ((let uu____1739 =
                      let uu____1740 =
                        let uu____1741 = FStar_Syntax_Subst.compress h' in
                        FStar_Syntax_Print.term_to_string uu____1741 in
                      Prims.strcat
                        "Type term not defined for higher-order type "
                        uu____1740 in
                    FStar_Util.print_warning uu____1739);
                   FStar_Exn.raise CallNotImplemented))
         | uu____1742 ->
             (FStar_Util.print_warning "Impossible\n";
              FStar_Exn.raise CallNotImplemented))
    | uu____1744 ->
        ((let uu____1746 =
            let uu____1747 =
              let uu____1748 = FStar_Syntax_Subst.compress t in
              FStar_Syntax_Print.term_to_string uu____1748 in
            Prims.strcat "Type term not defined for " uu____1747 in
          FStar_Util.print_warning uu____1746);
         FStar_Exn.raise CallNotImplemented)
let rec mk_tac_embedding_path:
  emb_decl -> FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun m  ->
    fun t  ->
      let uu____1755 =
        let uu____1756 = FStar_Syntax_Subst.compress t in
        uu____1756.FStar_Syntax_Syntax.n in
      match uu____1755 with
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
          let uu____1764 =
            FStar_Reflection_Data.fstar_refl_types_lid "binder" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1764 ->
          mk_embedding m "binder"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1766 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1766 ->
          mk_embedding m "term"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1768 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1768 ->
          mk_embedding m "fvar"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1770 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "binders" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1770 ->
          mk_embedding m "binders"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1772 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1772 ->
          mk_embedding m "norm_step"
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____1795 =
            let uu____1796 = FStar_Syntax_Subst.compress h in
            uu____1796.FStar_Syntax_Syntax.n in
          (match uu____1795 with
           | FStar_Syntax_Syntax.Tm_uinst (h',uu____1800) ->
               let uu____1805 =
                 let uu____1816 =
                   let uu____1817 = FStar_Syntax_Subst.compress h' in
                   uu____1817.FStar_Syntax_Syntax.n in
                 match uu____1816 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.list_lid
                     ->
                     let arg_term =
                       let uu____1834 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1834 in
                     let uu____1849 =
                       let uu____1852 = mk_tac_embedding_path m arg_term in
                       [uu____1852] in
                     let uu____1853 = mk_tac_param_type arg_term in
                     ("list", uu____1849, uu____1853, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.option_lid
                     ->
                     let arg_term =
                       let uu____1860 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1860 in
                     let uu____1875 =
                       let uu____1878 = mk_tac_embedding_path m arg_term in
                       [uu____1878] in
                     let uu____1879 = mk_tac_param_type arg_term in
                     ("option", uu____1875, uu____1879, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.tactic_lid
                     ->
                     let arg_term =
                       let uu____1886 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1886 in
                     let uu____1901 =
                       let uu____1904 = mk_tac_embedding_path m arg_term in
                       [uu____1904] in
                     let uu____1905 = mk_tac_param_type arg_term in
                     ("list", uu____1901, uu____1905, true)
                 | uu____1908 ->
                     ((let uu____1910 =
                         let uu____1911 =
                           let uu____1912 = FStar_Syntax_Subst.compress h' in
                           FStar_Syntax_Print.term_to_string uu____1912 in
                         Prims.strcat
                           "Embedding not defined for higher-order type "
                           uu____1911 in
                       FStar_Util.print_warning uu____1910);
                      FStar_Exn.raise CallNotImplemented) in
               (match uu____1805 with
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
                      (let uu____1938 =
                         let uu____1945 =
                           let uu____1946 = mk_basic_embedding m ht in
                           FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top uu____1946 in
                         let uu____1947 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top) hargs1 in
                         (uu____1945, uu____1947) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____1938))
           | uu____1952 ->
               (FStar_Util.print_warning "Impossible\n";
                FStar_Exn.raise CallNotImplemented))
      | uu____1954 ->
          ((let uu____1956 =
              let uu____1957 =
                let uu____1958 = FStar_Syntax_Subst.compress t in
                FStar_Syntax_Print.term_to_string uu____1958 in
              Prims.strcat "Embedding not defined for type " uu____1957 in
            FStar_Util.print_warning uu____1956);
           FStar_Exn.raise CallNotImplemented)
let mk_interpretation_fun:
  'Auu____1964 .
    FStar_Ident.lident ->
      FStar_Extraction_ML_Syntax.mlexpr' ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,'Auu____1964)
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
              let uu____2032 =
                let uu____2033 = FStar_Util.string_of_int arity in
                Prims.strcat
                  "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                  uu____2033 in
              str_to_top_name uu____2032 in
            let tac_fun =
              let uu____2041 =
                let uu____2048 =
                  let uu____2049 =
                    let uu____2050 = FStar_Util.string_of_int arity in
                    Prims.strcat "FStar_Tactics_Native.from_tactic_"
                      uu____2050 in
                  str_to_top_name uu____2049 in
                let uu____2057 =
                  let uu____2060 = lid_to_top_name tac_lid in [uu____2060] in
                (uu____2048, uu____2057) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2041 in
            let tac_lid_app =
              let uu____2064 =
                let uu____2071 = str_to_top_name "FStar_Ident.lid_of_str" in
                (uu____2071,
                  [FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.MLTY_Top assm_lid]) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2064 in
            let psc = str_to_name "psc" in
            let args =
              let uu____2078 =
                let uu____2081 =
                  FStar_List.map (mk_tac_embedding_path Unembed) arg_types in
                let uu____2084 =
                  let uu____2087 = mk_tac_embedding_path Embed t in
                  let uu____2088 =
                    let uu____2091 = mk_tac_param_type t in
                    let uu____2092 =
                      let uu____2095 =
                        let uu____2098 =
                          let uu____2101 = str_to_name "args" in [uu____2101] in
                        psc :: uu____2098 in
                      tac_lid_app :: uu____2095 in
                    uu____2091 :: uu____2092 in
                  uu____2087 :: uu____2088 in
                FStar_List.append uu____2081 uu____2084 in
              FStar_List.append [tac_fun] uu____2078 in
            let app =
              let uu____2103 =
                let uu____2104 =
                  let uu____2111 =
                    FStar_List.map
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top) args in
                  (h, uu____2111) in
                FStar_Extraction_ML_Syntax.MLE_App uu____2104 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2103 in
            FStar_Pervasives_Native.Some
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([("psc", FStar_Extraction_ML_Syntax.MLTY_Top);
                  ("args", FStar_Extraction_ML_Syntax.MLTY_Top)], app))
          with
          | CallNotImplemented  ->
              ((let uu____2140 = FStar_Ident.string_of_lid tac_lid in
                not_implemented_warning uu____2140);
               FStar_Pervasives_Native.None)