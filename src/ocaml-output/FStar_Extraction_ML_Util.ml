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
    | FStar_Const.Const_bytearray (bytes,uu____65) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____71) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____72 ->
        failwith "Unhandled constant: reify/reflect"
let mlconst_of_const':
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const c
      with
      | uu____87 ->
          let uu____88 =
            let uu____89 = FStar_Range.string_of_range p in
            let uu____90 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____89 uu____90 in
          failwith uu____88
let rec subst_aux:
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____112 =
            FStar_Util.find_opt
              (fun uu____126  ->
                 match uu____126 with | (y,uu____132) -> y = x) subst1 in
          (match uu____112 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____149 =
            let uu____156 = subst_aux subst1 t1 in
            let uu____157 = subst_aux subst1 t2 in (uu____156, f, uu____157) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____149
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____164 =
            let uu____171 = FStar_List.map (subst_aux subst1) args in
            (uu____171, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____164
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____179 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____179
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let try_subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun uu____192  ->
    fun args  ->
      match uu____192 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____203 =
               let uu____204 = FStar_List.zip formals args in
               subst_aux uu____204 t in
             FStar_Pervasives_Native.Some uu____203)
let subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun ts  ->
    fun args  ->
      let uu____223 = try_subst ts args in
      match uu____223 with
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
    fun uu___117_236  ->
      match uu___117_236 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____245 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____245 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____251 = try_subst ts args in
               (match uu____251 with
                | FStar_Pervasives_Native.None  ->
                    let uu____256 =
                      let uu____257 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1 in
                      let uu____258 =
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu____259 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____257 uu____258 uu____259 in
                    failwith uu____256
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____263 -> FStar_Pervasives_Native.None)
      | uu____266 -> FStar_Pervasives_Native.None
let eff_leq:
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____275) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____276 -> false
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___118_284  ->
    match uu___118_284 with
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
        | uu____297 ->
            let uu____302 =
              let uu____303 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____303
                (eff_to_string f) (eff_to_string f') in
            failwith uu____302
let join_l:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun:
  'Auu____322 .
    Prims.unit ->
      ('Auu____322,FStar_Extraction_ML_Syntax.mlty)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____333  ->
    FStar_List.fold_right
      (fun uu____342  ->
         fun t  ->
           match uu____342 with
           | (uu____348,t0) ->
               FStar_Extraction_ML_Syntax.MLTY_Fun
                 (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
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
              if
                (FStar_Pervasives_Native.fst x) =
                  (FStar_Pervasives_Native.fst y)
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Fun
             (t1,f,t2),FStar_Extraction_ML_Syntax.MLTY_Fun (t1',f',t2')) ->
              let mk_fun xs body =
                match xs with
                | [] -> body
                | uu____435 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____467 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____474 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____474 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____484;
                     FStar_Extraction_ML_Syntax.loc = uu____485;_}
                   ->
                   let uu____506 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____506
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____522 = type_leq unfold_ty t2 t2' in
                        (if uu____522
                         then
                           let body1 =
                             let uu____533 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____533
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____538 =
                             let uu____541 =
                               let uu____542 =
                                 let uu____545 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____545 in
                               FStar_All.pipe_left uu____542
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu____541 in
                           (true, uu____538)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____574 =
                           let uu____581 =
                             let uu____584 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun _0_42  ->
                                  FStar_Pervasives_Native.Some _0_42)
                               uu____584 in
                           type_leq_c unfold_ty uu____581 t2 t2' in
                         match uu____574 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____608 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu____608
                               | uu____617 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____625 ->
                   let uu____628 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____628
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____664 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____664
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____680 = unfold_ty t in
                 match uu____680 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____694 = unfold_ty t' in
                     (match uu____694 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____716 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____716
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____733,uu____734) ->
              let uu____741 = unfold_ty t in
              (match uu____741 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____755 -> (false, FStar_Pervasives_Native.None))
          | (uu____760,FStar_Extraction_ML_Syntax.MLTY_Named uu____761) ->
              let uu____768 = unfold_ty t' in
              (match uu____768 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____782 -> (false, FStar_Pervasives_Native.None))
          | uu____787 -> (false, FStar_Pervasives_Native.None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____798 = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_All.pipe_right uu____798 FStar_Pervasives_Native.fst
let is_type_abstraction:
  'Auu____824 'Auu____825 'Auu____826 .
    (('Auu____826,'Auu____825) FStar_Util.either,'Auu____824)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun uu___119_840  ->
    match uu___119_840 with
    | (FStar_Util.Inl uu____851,uu____852)::uu____853 -> true
    | uu____876 -> false
let is_xtuple:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____898  ->
    match uu____898 with
    | (ns,n1) ->
        let uu____913 =
          let uu____914 = FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_datacon_string uu____914 in
        if uu____913
        then
          let uu____917 =
            let uu____918 = FStar_Util.char_at n1 (Prims.parse_int "7") in
            FStar_Util.int_of_char uu____918 in
          FStar_Pervasives_Native.Some uu____917
        else FStar_Pervasives_Native.None
let resugar_exp:
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____930 = is_xtuple mlp in
        (match uu____930 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____934 -> e)
    | uu____937 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___120_945  ->
    match uu___120_945 with
    | f::uu____951 ->
        let uu____954 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____954 with
         | (ns,uu____964) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____975 -> failwith "impos"
let record_fields:
  'Auu____986 .
    FStar_Ident.lident Prims.list ->
      'Auu____986 Prims.list ->
        (Prims.string,'Auu____986) FStar_Pervasives_Native.tuple2 Prims.list
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
  fun uu____1028  ->
    match uu____1028 with
    | (ns,n1) ->
        let uu____1043 =
          let uu____1044 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_constructor_string uu____1044 in
        if uu____1043
        then
          let uu____1047 =
            let uu____1048 = FStar_Util.char_at n1 (Prims.parse_int "5") in
            FStar_Util.int_of_char uu____1048 in
          FStar_Pervasives_Native.Some uu____1047
        else FStar_Pervasives_Native.None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1060 = is_xtuple_ty mlp in
        (match uu____1060 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1064 -> t)
    | uu____1067 -> t
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____1071  ->
    let uu____1072 =
      let uu____1073 = FStar_Options.codegen () in
      FStar_Option.get uu____1073 in
    uu____1072 = "FSharp"
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____1084 = codegen_fsharp () in
    if uu____1084
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string
  =
  fun uu____1095  ->
    match uu____1095 with
    | (ns,n1) ->
        let uu____1108 = codegen_fsharp () in
        if uu____1108
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____1120 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____1120, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____1143 = unfold_ty t in
         match uu____1143 with
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
            let uu____1165 =
              let uu____1172 = eraseTypeDeep unfold_ty tyd in
              let uu____1176 = eraseTypeDeep unfold_ty tycd in
              (uu____1172, etag, uu____1176) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1165
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1187 = erasableType unfold_ty t in
          if uu____1187
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1192 =
               let uu____1199 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____1199, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1192)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1210 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1210
      | uu____1216 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____1219 =
    let uu____1222 =
      (mk_ty_fun ())
        [(("x", (Prims.parse_int "0")),
           FStar_Extraction_ML_Syntax.ml_bool_ty);
        (("y", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____1222 in
  FStar_All.pipe_left uu____1219
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
          let uu____1315 = conjoin x y in
          FStar_Pervasives_Native.Some uu____1315
let mlloc_of_range:
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____1326 = FStar_Range.file_of_range r in (line, uu____1326)
let rec doms_and_cod:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1344,b) ->
        let uu____1346 = doms_and_cod b in
        (match uu____1346 with | (ds,c) -> ((a :: ds), c))
    | uu____1367 -> ([], t)
let argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    let uu____1378 = doms_and_cod t in FStar_Pervasives_Native.fst uu____1378
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1404,b) ->
        let uu____1406 = uncurry_mlty_fun b in
        (match uu____1406 with | (args,res) -> ((a :: args), res))
    | uu____1427 -> ([], t)
type emb_decl =
  | Embed
  | Unembed
let uu___is_Embed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____1434 -> false
let uu___is_Unembed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____1439 -> false
let lid_to_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun l  ->
    let uu____1444 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
    FStar_Extraction_ML_Syntax.MLE_Name uu____1444
let lid_to_top_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun l  ->
    let uu____1449 =
      let uu____1450 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
      FStar_Extraction_ML_Syntax.MLE_Name uu____1450 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1449
let str_to_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  ->
    let uu____1455 = FStar_Ident.lid_of_str s in lid_to_name uu____1455
let str_to_top_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr =
  fun s  ->
    let uu____1460 = FStar_Ident.lid_of_str s in lid_to_top_name uu____1460
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
      let uu____1507 =
        let uu____1508 =
          let uu____1515 =
            str_to_top_name "FStar_Tactics_Interpreter.reify_tactic" in
          let uu____1516 =
            let uu____1519 = str_to_top_name tac_arg in [uu____1519] in
          (uu____1515, uu____1516) in
        FStar_Extraction_ML_Syntax.MLE_App uu____1508 in
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1507 in
    let from_tac =
      let uu____1523 =
        let uu____1524 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Builtins.from_tac_" uu____1524 in
      str_to_top_name uu____1523 in
    let unembed_tactic =
      let uu____1526 =
        let uu____1527 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Interpreter.unembed_tactic_" uu____1527 in
      str_to_top_name uu____1526 in
    let app =
      match FStar_List.length args with
      | _0_43 when _0_43 = (Prims.parse_int "1") ->
          let uu____1529 =
            let uu____1536 =
              let uu____1539 =
                let uu____1540 =
                  let uu____1541 =
                    let uu____1548 =
                      let uu____1551 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) args in
                      FStar_List.append uu____1551 [reify_tactic] in
                    (unembed_tactic, uu____1548) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1541 in
                FStar_Extraction_ML_Syntax.with_ty
                  FStar_Extraction_ML_Syntax.MLTY_Top uu____1540 in
              [uu____1539] in
            (from_tac, uu____1536) in
          FStar_Extraction_ML_Syntax.MLE_App uu____1529
      | n1 ->
          let uu____1559 =
            let uu____1560 =
              let uu____1563 = FStar_Util.string_of_int n1 in [uu____1563] in
            FStar_Util.format
              "Unembedding not defined for tactics of %d arguments"
              uu____1560 in
          failwith uu____1559 in
    FStar_Extraction_ML_Syntax.MLE_Fun
      ([((tac_arg, (Prims.parse_int "0")),
          FStar_Extraction_ML_Syntax.MLTY_Top);
       (("()", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.MLTY_Top)],
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top app))
let rec mk_tac_param_type:
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun t  ->
    let uu____1616 =
      let uu____1617 = FStar_Syntax_Subst.compress t in
      uu____1617.FStar_Syntax_Syntax.n in
    match uu____1616 with
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
        let uu____1625 = FStar_Reflection_Data.fstar_refl_types_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1625 ->
        fstar_refl_data_prefix "t_binder"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1627 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1627 ->
        fstar_refl_data_prefix "t_term"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1629 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1629 ->
        fstar_refl_data_prefix "t_fv"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1631 = FStar_Reflection_Data.fstar_refl_syntax_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1631 ->
        fstar_refl_data_prefix "t_binders"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1633 =
          FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1633 ->
        fstar_refl_data_prefix "t_norm_step"
    | FStar_Syntax_Syntax.Tm_app (h,args) ->
        let uu____1656 =
          let uu____1657 = FStar_Syntax_Subst.compress h in
          uu____1657.FStar_Syntax_Syntax.n in
        (match uu____1656 with
         | FStar_Syntax_Syntax.Tm_uinst (h',uu____1661) ->
             let uu____1666 =
               let uu____1667 = FStar_Syntax_Subst.compress h' in
               uu____1667.FStar_Syntax_Syntax.n in
             (match uu____1666 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.list_lid
                  ->
                  let arg_term =
                    let uu____1674 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1674 in
                  let uu____1689 =
                    let uu____1696 =
                      let uu____1697 = fstar_tc_common_prefix "t_list_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1697 in
                    let uu____1698 =
                      let uu____1701 =
                        let uu____1704 = mk_tac_param_type arg_term in
                        [uu____1704] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1701 in
                    (uu____1696, uu____1698) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1689
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.option_lid
                  ->
                  let arg_term =
                    let uu____1711 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1711 in
                  let uu____1726 =
                    let uu____1733 =
                      let uu____1734 = fstar_tc_common_prefix "t_option_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1734 in
                    let uu____1735 =
                      let uu____1738 =
                        let uu____1741 = mk_tac_param_type arg_term in
                        [uu____1741] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1738 in
                    (uu____1733, uu____1735) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1726
              | uu____1744 ->
                  let uu____1745 =
                    let uu____1746 =
                      let uu____1747 = FStar_Syntax_Subst.compress h' in
                      FStar_Syntax_Print.term_to_string uu____1747 in
                    Prims.strcat
                      "Type term not defined for higher-order type "
                      uu____1746 in
                  failwith uu____1745)
         | uu____1748 -> failwith "Impossible")
    | uu____1749 ->
        let uu____1750 =
          let uu____1751 =
            let uu____1752 = FStar_Syntax_Subst.compress t in
            FStar_Syntax_Print.term_to_string uu____1752 in
          Prims.strcat "Type term not defined for " uu____1751 in
        failwith uu____1750
let rec mk_tac_embedding_path:
  emb_decl -> FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun m  ->
    fun t  ->
      let uu____1761 =
        let uu____1762 = FStar_Syntax_Subst.compress t in
        uu____1762.FStar_Syntax_Syntax.n in
      match uu____1761 with
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
          let uu____1770 =
            FStar_Reflection_Data.fstar_refl_types_lid "binder" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1770 ->
          mk_embedding m "binder"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1772 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1772 ->
          mk_embedding m "term"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1774 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1774 ->
          mk_embedding m "fvar"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1776 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "binders" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1776 ->
          mk_embedding m "binders"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1778 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1778 ->
          mk_embedding m "norm_step"
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____1801 =
            let uu____1802 = FStar_Syntax_Subst.compress h in
            uu____1802.FStar_Syntax_Syntax.n in
          (match uu____1801 with
           | FStar_Syntax_Syntax.Tm_uinst (h',uu____1806) ->
               let uu____1811 =
                 let uu____1822 =
                   let uu____1823 = FStar_Syntax_Subst.compress h' in
                   uu____1823.FStar_Syntax_Syntax.n in
                 match uu____1822 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.list_lid
                     ->
                     let arg_term =
                       let uu____1840 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1840 in
                     let uu____1855 =
                       let uu____1858 = mk_tac_embedding_path m arg_term in
                       [uu____1858] in
                     let uu____1859 = mk_tac_param_type arg_term in
                     ("list", uu____1855, uu____1859, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.option_lid
                     ->
                     let arg_term =
                       let uu____1866 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1866 in
                     let uu____1881 =
                       let uu____1884 = mk_tac_embedding_path m arg_term in
                       [uu____1884] in
                     let uu____1885 = mk_tac_param_type arg_term in
                     ("option", uu____1881, uu____1885, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.tactic_lid
                     ->
                     let arg_term =
                       let uu____1892 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1892 in
                     let uu____1907 =
                       let uu____1910 = mk_tac_embedding_path m arg_term in
                       [uu____1910] in
                     let uu____1911 = mk_tac_param_type arg_term in
                     ("list", uu____1907, uu____1911, true)
                 | uu____1914 ->
                     let uu____1915 =
                       let uu____1916 =
                         let uu____1917 = FStar_Syntax_Subst.compress h' in
                         FStar_Syntax_Print.term_to_string uu____1917 in
                       Prims.strcat
                         "Embedding not defined for higher-order type "
                         uu____1916 in
                     failwith uu____1915 in
               (match uu____1811 with
                | (ht,hargs,type_arg,is_tactic) ->
                    let hargs1 =
                      match m with
                      | Embed  -> FStar_List.append hargs [type_arg]
                      | Unembed  -> hargs in
                    if is_tactic
                    then
                      (match m with
                       | Embed  ->
                           failwith "Embedding not defined for tactic type"
                       | Unembed  -> mk_tactic_unembedding hargs1)
                    else
                      (let uu____1942 =
                         let uu____1949 =
                           let uu____1950 = mk_basic_embedding m ht in
                           FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top uu____1950 in
                         let uu____1951 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top) hargs1 in
                         (uu____1949, uu____1951) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____1942))
           | uu____1956 -> failwith "Impossible")
      | uu____1957 ->
          let uu____1958 =
            let uu____1959 =
              let uu____1960 = FStar_Syntax_Subst.compress t in
              FStar_Syntax_Print.term_to_string uu____1960 in
            Prims.strcat "Embedding not defined for type " uu____1959 in
          failwith uu____1958
let mk_interpretation_fun:
  'Auu____1971 .
    FStar_Ident.lident ->
      FStar_Extraction_ML_Syntax.mlexpr' ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,'Auu____1971)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun tac_lid  ->
    fun assm_lid  ->
      fun t  ->
        fun bs  ->
          let arg_types =
            FStar_List.map
              (fun x  ->
                 (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort) bs in
          let arity = FStar_List.length bs in
          let h =
            let uu____2023 =
              let uu____2024 = FStar_Util.string_of_int arity in
              Prims.strcat
                "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                uu____2024 in
            str_to_top_name uu____2023 in
          let tac_fun =
            let uu____2032 =
              let uu____2039 =
                let uu____2040 =
                  let uu____2041 = FStar_Util.string_of_int arity in
                  Prims.strcat "FStar_Tactics_Native.from_tactic_" uu____2041 in
                str_to_top_name uu____2040 in
              let uu____2048 =
                let uu____2051 = lid_to_top_name tac_lid in [uu____2051] in
              (uu____2039, uu____2048) in
            FStar_Extraction_ML_Syntax.MLE_App uu____2032 in
          let tac_lid_app =
            let uu____2055 =
              let uu____2062 = str_to_top_name "FStar_Ident.lid_of_str" in
              (uu____2062,
                [FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top assm_lid]) in
            FStar_Extraction_ML_Syntax.MLE_App uu____2055 in
          let args =
            let uu____2068 =
              let uu____2071 = str_to_name "ps" in [uu____2071; tac_fun] in
            let uu____2072 =
              let uu____2075 =
                FStar_List.map (mk_tac_embedding_path Unembed) arg_types in
              let uu____2078 =
                let uu____2081 = mk_tac_embedding_path Embed t in
                let uu____2082 =
                  let uu____2085 = mk_tac_param_type t in
                  let uu____2086 =
                    let uu____2089 =
                      let uu____2092 = str_to_name "args" in [uu____2092] in
                    tac_lid_app :: uu____2089 in
                  uu____2085 :: uu____2086 in
                uu____2081 :: uu____2082 in
              FStar_List.append uu____2075 uu____2078 in
            FStar_List.append uu____2068 uu____2072 in
          let app =
            let uu____2094 =
              let uu____2095 =
                let uu____2102 =
                  FStar_List.map
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.MLTY_Top) args in
                (h, uu____2102) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2095 in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____2094 in
          FStar_Extraction_ML_Syntax.MLE_Fun
            ([(("ps", (Prims.parse_int "0")),
                FStar_Extraction_ML_Syntax.MLTY_Top);
             (("args", (Prims.parse_int "0")),
               FStar_Extraction_ML_Syntax.MLTY_Top)], app)