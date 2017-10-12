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
let mlconst_of_const:
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant =
  fun sctt  ->
    match sctt with
    | FStar_Const.Const_range uu____40 -> failwith "Unsupported constant"
    | FStar_Const.Const_effect  -> failwith "Unsupported constant"
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____74) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____80) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____81 ->
        failwith "Unhandled constant: reify/reflect"
let mlconst_of_const':
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const c
      with
      | uu____96 ->
          let uu____97 =
            let uu____98 = FStar_Range.string_of_range p in
            let uu____99 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____98 uu____99 in
          failwith uu____97
let rec subst_aux:
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____121 =
            FStar_Util.find_opt
              (fun uu____135  ->
                 match uu____135 with | (y,uu____141) -> y = x) subst1 in
          (match uu____121 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____158 =
            let uu____165 = subst_aux subst1 t1 in
            let uu____166 = subst_aux subst1 t2 in (uu____165, f, uu____166) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____158
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____173 =
            let uu____180 = FStar_List.map (subst_aux subst1) args in
            (uu____180, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____173
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____188 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____188
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let try_subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun uu____201  ->
    fun args  ->
      match uu____201 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____212 =
               let uu____213 = FStar_List.zip formals args in
               subst_aux uu____213 t in
             FStar_Pervasives_Native.Some uu____212)
let subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun ts  ->
    fun args  ->
      let uu____232 = try_subst ts args in
      match uu____232 with
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
    fun uu___140_245  ->
      match uu___140_245 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____254 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____254 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____260 = try_subst ts args in
               (match uu____260 with
                | FStar_Pervasives_Native.None  ->
                    let uu____265 =
                      let uu____266 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1 in
                      let uu____267 =
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu____268 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____266 uu____267 uu____268 in
                    failwith uu____265
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____272 -> FStar_Pervasives_Native.None)
      | uu____275 -> FStar_Pervasives_Native.None
let eff_leq:
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____284) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____285 -> false
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___141_293  ->
    match uu___141_293 with
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
        | uu____306 ->
            let uu____311 =
              let uu____312 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____312
                (eff_to_string f) (eff_to_string f') in
            failwith uu____311
let join_l:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun:
  'Auu____331 .
    Prims.unit ->
      ('Auu____331,FStar_Extraction_ML_Syntax.mlty)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____342  ->
    FStar_List.fold_right
      (fun uu____351  ->
         fun t  ->
           match uu____351 with
           | (uu____357,t0) ->
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
                | uu____444 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____476 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____483 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____483 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____493;
                     FStar_Extraction_ML_Syntax.loc = uu____494;_}
                   ->
                   let uu____515 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____515
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____531 = type_leq unfold_ty t2 t2' in
                        (if uu____531
                         then
                           let body1 =
                             let uu____542 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____542
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____547 =
                             let uu____550 =
                               let uu____551 =
                                 let uu____554 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____554 in
                               FStar_All.pipe_left uu____551
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu____550 in
                           (true, uu____547)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____583 =
                           let uu____590 =
                             let uu____593 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun _0_42  ->
                                  FStar_Pervasives_Native.Some _0_42)
                               uu____593 in
                           type_leq_c unfold_ty uu____590 t2 t2' in
                         match uu____583 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____617 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu____617
                               | uu____626 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____634 ->
                   let uu____637 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____637
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____673 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____673
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____689 = unfold_ty t in
                 match uu____689 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____703 = unfold_ty t' in
                     (match uu____703 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____725 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____725
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____742,uu____743) ->
              let uu____750 = unfold_ty t in
              (match uu____750 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____764 -> (false, FStar_Pervasives_Native.None))
          | (uu____769,FStar_Extraction_ML_Syntax.MLTY_Named uu____770) ->
              let uu____777 = unfold_ty t' in
              (match uu____777 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____791 -> (false, FStar_Pervasives_Native.None))
          | uu____796 -> (false, FStar_Pervasives_Native.None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____807 = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_All.pipe_right uu____807 FStar_Pervasives_Native.fst
let is_type_abstraction:
  'Auu____833 'Auu____834 'Auu____835 .
    (('Auu____835,'Auu____834) FStar_Util.either,'Auu____833)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun uu___142_849  ->
    match uu___142_849 with
    | (FStar_Util.Inl uu____860,uu____861)::uu____862 -> true
    | uu____885 -> false
let is_xtuple:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____907  ->
    match uu____907 with
    | (ns,n1) ->
        let uu____922 =
          let uu____923 = FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_datacon_string uu____923 in
        if uu____922
        then
          let uu____926 =
            let uu____927 = FStar_Util.char_at n1 (Prims.parse_int "7") in
            FStar_Util.int_of_char uu____927 in
          FStar_Pervasives_Native.Some uu____926
        else FStar_Pervasives_Native.None
let resugar_exp:
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____948 = is_xtuple mlp in
        (match uu____948 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____952 -> e)
    | uu____955 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___143_963  ->
    match uu___143_963 with
    | f::uu____969 ->
        let uu____972 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____972 with
         | (ns,uu____982) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____993 -> failwith "impos"
let record_fields:
  'Auu____1004 .
    FStar_Ident.lident Prims.list ->
      'Auu____1004 Prims.list ->
        (Prims.string,'Auu____1004) FStar_Pervasives_Native.tuple2 Prims.list
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
  fun uu____1046  ->
    match uu____1046 with
    | (ns,n1) ->
        let uu____1061 =
          let uu____1062 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_constructor_string uu____1062 in
        if uu____1061
        then
          let uu____1065 =
            let uu____1066 = FStar_Util.char_at n1 (Prims.parse_int "5") in
            FStar_Util.int_of_char uu____1066 in
          FStar_Pervasives_Native.Some uu____1065
        else FStar_Pervasives_Native.None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1087 = is_xtuple_ty mlp in
        (match uu____1087 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1091 -> t)
    | uu____1094 -> t
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____1098  ->
    let uu____1099 =
      let uu____1100 = FStar_Options.codegen () in
      FStar_Option.get uu____1100 in
    uu____1099 = "FSharp"
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____1111 = codegen_fsharp () in
    if uu____1111
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string
  =
  fun uu____1122  ->
    match uu____1122 with
    | (ns,n1) ->
        let uu____1135 = codegen_fsharp () in
        if uu____1135
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____1147 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____1147, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____1170 = unfold_ty t in
         match uu____1170 with
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
            let uu____1192 =
              let uu____1199 = eraseTypeDeep unfold_ty tyd in
              let uu____1203 = eraseTypeDeep unfold_ty tycd in
              (uu____1199, etag, uu____1203) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1192
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1214 = erasableType unfold_ty t in
          if uu____1214
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1219 =
               let uu____1226 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____1226, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1219)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1237 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1237
      | uu____1243 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____1246 =
    let uu____1249 =
      (mk_ty_fun ())
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____1249 in
  FStar_All.pipe_left uu____1246
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
          let uu____1318 = conjoin x y in
          FStar_Pervasives_Native.Some uu____1318
let mlloc_of_range:
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____1329 = FStar_Range.file_of_range r in (line, uu____1329)
let rec doms_and_cod:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1347,b) ->
        let uu____1349 = doms_and_cod b in
        (match uu____1349 with | (ds,c) -> ((a :: ds), c))
    | uu____1370 -> ([], t)
let argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    let uu____1381 = doms_and_cod t in FStar_Pervasives_Native.fst uu____1381
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1407,b) ->
        let uu____1409 = uncurry_mlty_fun b in
        (match uu____1409 with | (args,res) -> ((a :: args), res))
    | uu____1430 -> ([], t)
exception CallNotImplemented
let uu___is_CallNotImplemented: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | CallNotImplemented  -> true | uu____1437 -> false
let not_implemented_warning: Prims.string -> Prims.unit =
  fun t  ->
    let uu____1442 =
      FStar_Util.format1 ". Tactic %s will not run natively.\n" t in
    FStar_All.pipe_right uu____1442 FStar_Util.print_warning
type emb_decl =
  | Embed
  | Unembed[@@deriving show]
let uu___is_Embed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____1447 -> false
let uu___is_Unembed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____1452 -> false
let lid_to_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun l  ->
    let uu____1457 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
    FStar_Extraction_ML_Syntax.MLE_Name uu____1457
let lid_to_top_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun l  ->
    let uu____1462 =
      let uu____1463 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
      FStar_Extraction_ML_Syntax.MLE_Name uu____1463 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1462
let str_to_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  ->
    let uu____1468 = FStar_Ident.lid_of_str s in lid_to_name uu____1468
let str_to_top_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr =
  fun s  ->
    let uu____1473 = FStar_Ident.lid_of_str s in lid_to_top_name uu____1473
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
      let uu____1520 =
        let uu____1521 =
          let uu____1528 =
            str_to_top_name "FStar_Tactics_Interpreter.reify_tactic" in
          let uu____1529 =
            let uu____1532 = str_to_top_name tac_arg in [uu____1532] in
          (uu____1528, uu____1529) in
        FStar_Extraction_ML_Syntax.MLE_App uu____1521 in
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1520 in
    let from_tac =
      let uu____1536 =
        let uu____1537 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Builtins.from_tac_" uu____1537 in
      str_to_top_name uu____1536 in
    let unembed_tactic =
      let uu____1539 =
        let uu____1540 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Interpreter.unembed_tactic_" uu____1540 in
      str_to_top_name uu____1539 in
    let app =
      match FStar_List.length args with
      | _0_43 when _0_43 = (Prims.parse_int "1") ->
          let uu____1542 =
            let uu____1549 =
              let uu____1552 =
                let uu____1553 =
                  let uu____1554 =
                    let uu____1561 =
                      let uu____1564 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) args in
                      FStar_List.append uu____1564 [reify_tactic] in
                    (unembed_tactic, uu____1561) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1554 in
                FStar_Extraction_ML_Syntax.with_ty
                  FStar_Extraction_ML_Syntax.MLTY_Top uu____1553 in
              [uu____1552] in
            (from_tac, uu____1549) in
          FStar_Extraction_ML_Syntax.MLE_App uu____1542
      | n1 ->
          ((let uu____1573 =
              let uu____1574 =
                let uu____1577 = FStar_Util.string_of_int n1 in [uu____1577] in
              FStar_Util.format
                "Unembedding not defined for tactics of %d arguments"
                uu____1574 in
            FStar_Util.print_warning uu____1573);
           FStar_Exn.raise CallNotImplemented) in
    FStar_Extraction_ML_Syntax.MLE_Fun
      ([(tac_arg, FStar_Extraction_ML_Syntax.MLTY_Top);
       ("()", FStar_Extraction_ML_Syntax.MLTY_Top)],
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top app))
let rec mk_tac_param_type:
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun t  ->
    let uu____1606 =
      let uu____1607 = FStar_Syntax_Subst.compress t in
      uu____1607.FStar_Syntax_Syntax.n in
    match uu____1606 with
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
        let uu____1615 = FStar_Reflection_Data.fstar_refl_types_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1615 ->
        fstar_refl_data_prefix "t_binder"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1617 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1617 ->
        fstar_refl_data_prefix "t_term"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1619 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1619 ->
        fstar_refl_data_prefix "t_fv"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1621 = FStar_Reflection_Data.fstar_refl_syntax_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1621 ->
        fstar_refl_data_prefix "t_binders"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1623 =
          FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1623 ->
        fstar_refl_data_prefix "t_norm_step"
    | FStar_Syntax_Syntax.Tm_app (h,args) ->
        let uu____1646 =
          let uu____1647 = FStar_Syntax_Subst.compress h in
          uu____1647.FStar_Syntax_Syntax.n in
        (match uu____1646 with
         | FStar_Syntax_Syntax.Tm_uinst (h',uu____1651) ->
             let uu____1656 =
               let uu____1657 = FStar_Syntax_Subst.compress h' in
               uu____1657.FStar_Syntax_Syntax.n in
             (match uu____1656 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.list_lid
                  ->
                  let arg_term =
                    let uu____1664 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1664 in
                  let uu____1679 =
                    let uu____1686 =
                      let uu____1687 = fstar_tc_common_prefix "t_list_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1687 in
                    let uu____1688 =
                      let uu____1691 =
                        let uu____1694 = mk_tac_param_type arg_term in
                        [uu____1694] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1691 in
                    (uu____1686, uu____1688) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1679
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.option_lid
                  ->
                  let arg_term =
                    let uu____1701 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1701 in
                  let uu____1716 =
                    let uu____1723 =
                      let uu____1724 = fstar_tc_common_prefix "t_option_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1724 in
                    let uu____1725 =
                      let uu____1728 =
                        let uu____1731 = mk_tac_param_type arg_term in
                        [uu____1731] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1728 in
                    (uu____1723, uu____1725) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1716
              | uu____1734 ->
                  ((let uu____1736 =
                      let uu____1737 =
                        let uu____1738 = FStar_Syntax_Subst.compress h' in
                        FStar_Syntax_Print.term_to_string uu____1738 in
                      Prims.strcat
                        "Type term not defined for higher-order type "
                        uu____1737 in
                    FStar_Util.print_warning uu____1736);
                   FStar_Exn.raise CallNotImplemented))
         | uu____1739 ->
             (FStar_Util.print_warning "Impossible";
              FStar_Exn.raise CallNotImplemented))
    | uu____1741 ->
        ((let uu____1743 =
            let uu____1744 =
              let uu____1745 = FStar_Syntax_Subst.compress t in
              FStar_Syntax_Print.term_to_string uu____1745 in
            Prims.strcat "Type term not defined for " uu____1744 in
          FStar_Util.print_warning uu____1743);
         FStar_Exn.raise CallNotImplemented)
let rec mk_tac_embedding_path:
  emb_decl -> FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun m  ->
    fun t  ->
      let uu____1754 =
        let uu____1755 = FStar_Syntax_Subst.compress t in
        uu____1755.FStar_Syntax_Syntax.n in
      match uu____1754 with
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
          let uu____1763 =
            FStar_Reflection_Data.fstar_refl_types_lid "binder" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1763 ->
          mk_embedding m "binder"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1765 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1765 ->
          mk_embedding m "term"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1767 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1767 ->
          mk_embedding m "fvar"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1769 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "binders" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1769 ->
          mk_embedding m "binders"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1771 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1771 ->
          mk_embedding m "norm_step"
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____1794 =
            let uu____1795 = FStar_Syntax_Subst.compress h in
            uu____1795.FStar_Syntax_Syntax.n in
          (match uu____1794 with
           | FStar_Syntax_Syntax.Tm_uinst (h',uu____1799) ->
               let uu____1804 =
                 let uu____1815 =
                   let uu____1816 = FStar_Syntax_Subst.compress h' in
                   uu____1816.FStar_Syntax_Syntax.n in
                 match uu____1815 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.list_lid
                     ->
                     let arg_term =
                       let uu____1833 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1833 in
                     let uu____1848 =
                       let uu____1851 = mk_tac_embedding_path m arg_term in
                       [uu____1851] in
                     let uu____1852 = mk_tac_param_type arg_term in
                     ("list", uu____1848, uu____1852, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.option_lid
                     ->
                     let arg_term =
                       let uu____1859 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1859 in
                     let uu____1874 =
                       let uu____1877 = mk_tac_embedding_path m arg_term in
                       [uu____1877] in
                     let uu____1878 = mk_tac_param_type arg_term in
                     ("option", uu____1874, uu____1878, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.tactic_lid
                     ->
                     let arg_term =
                       let uu____1885 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1885 in
                     let uu____1900 =
                       let uu____1903 = mk_tac_embedding_path m arg_term in
                       [uu____1903] in
                     let uu____1904 = mk_tac_param_type arg_term in
                     ("list", uu____1900, uu____1904, true)
                 | uu____1907 ->
                     ((let uu____1909 =
                         let uu____1910 =
                           let uu____1911 = FStar_Syntax_Subst.compress h' in
                           FStar_Syntax_Print.term_to_string uu____1911 in
                         Prims.strcat
                           "Embedding not defined for higher-order type "
                           uu____1910 in
                       FStar_Util.print_warning uu____1909);
                      FStar_Exn.raise CallNotImplemented) in
               (match uu____1804 with
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
                              "Embedding not defined for tactic type";
                            FStar_Exn.raise CallNotImplemented)
                       | Unembed  -> mk_tactic_unembedding hargs1)
                    else
                      (let uu____1937 =
                         let uu____1944 =
                           let uu____1945 = mk_basic_embedding m ht in
                           FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top uu____1945 in
                         let uu____1946 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top) hargs1 in
                         (uu____1944, uu____1946) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____1937))
           | uu____1951 ->
               (FStar_Util.print_warning "Impossible";
                FStar_Exn.raise CallNotImplemented))
      | uu____1953 ->
          ((let uu____1955 =
              let uu____1956 =
                let uu____1957 = FStar_Syntax_Subst.compress t in
                FStar_Syntax_Print.term_to_string uu____1957 in
              Prims.strcat "Embedding not defined for type " uu____1956 in
            FStar_Util.print_warning uu____1955);
           FStar_Exn.raise CallNotImplemented)
let mk_interpretation_fun:
  'Auu____1968 .
    FStar_Ident.lident ->
      FStar_Extraction_ML_Syntax.mlexpr' ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,'Auu____1968)
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
              let uu____2035 =
                let uu____2036 = FStar_Util.string_of_int arity in
                Prims.strcat
                  "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                  uu____2036 in
              str_to_top_name uu____2035 in
            let tac_fun =
              let uu____2044 =
                let uu____2051 =
                  let uu____2052 =
                    let uu____2053 = FStar_Util.string_of_int arity in
                    Prims.strcat "FStar_Tactics_Native.from_tactic_"
                      uu____2053 in
                  str_to_top_name uu____2052 in
                let uu____2060 =
                  let uu____2063 = lid_to_top_name tac_lid in [uu____2063] in
                (uu____2051, uu____2060) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2044 in
            let tac_lid_app =
              let uu____2067 =
                let uu____2074 = str_to_top_name "FStar_Ident.lid_of_str" in
                (uu____2074,
                  [FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.MLTY_Top assm_lid]) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2067 in
            let args =
              let uu____2080 =
                let uu____2083 = str_to_name "ps" in [uu____2083; tac_fun] in
              let uu____2084 =
                let uu____2087 =
                  FStar_List.map (mk_tac_embedding_path Unembed) arg_types in
                let uu____2090 =
                  let uu____2093 = mk_tac_embedding_path Embed t in
                  let uu____2094 =
                    let uu____2097 = mk_tac_param_type t in
                    let uu____2098 =
                      let uu____2101 =
                        let uu____2104 = str_to_name "args" in [uu____2104] in
                      tac_lid_app :: uu____2101 in
                    uu____2097 :: uu____2098 in
                  uu____2093 :: uu____2094 in
                FStar_List.append uu____2087 uu____2090 in
              FStar_List.append uu____2080 uu____2084 in
            let app =
              let uu____2106 =
                let uu____2107 =
                  let uu____2114 =
                    FStar_List.map
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top) args in
                  (h, uu____2114) in
                FStar_Extraction_ML_Syntax.MLE_App uu____2107 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2106 in
            FStar_Pervasives_Native.Some
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([("ps", FStar_Extraction_ML_Syntax.MLTY_Top);
                  ("args", FStar_Extraction_ML_Syntax.MLTY_Top)], app))
          with
          | CallNotImplemented  ->
              ((let uu____2143 = FStar_Ident.string_of_lid tac_lid in
                not_implemented_warning uu____2143);
               FStar_Pervasives_Native.None)