open Prims
let pruneNones l =
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
    | FStar_Const.Const_string (bytes,uu____71) ->
        FStar_Extraction_ML_Syntax.MLC_String
          (FStar_Util.string_of_unicode bytes)
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____76 ->
        failwith "Unhandled constant: reify/reflect"
let mlconst_of_const':
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const c
      with
      | uu____91 ->
          let uu____92 =
            let uu____93 = FStar_Range.string_of_range p in
            let uu____94 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____93 uu____94 in
          failwith uu____92
let rec subst_aux:
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____116 =
            FStar_Util.find_opt
              (fun uu____130  ->
                 match uu____130 with | (y,uu____136) -> y = x) subst1 in
          (match uu____116 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____153 =
            let uu____160 = subst_aux subst1 t1 in
            let uu____161 = subst_aux subst1 t2 in (uu____160, f, uu____161) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____153
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____168 =
            let uu____175 = FStar_List.map (subst_aux subst1) args in
            (uu____175, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____168
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____183 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____183
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let try_subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun uu____196  ->
    fun args  ->
      match uu____196 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____207 =
               let uu____208 = FStar_List.zip formals args in
               subst_aux uu____208 t in
             FStar_Pervasives_Native.Some uu____207)
let subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun ts  ->
    fun args  ->
      let uu____227 = try_subst ts args in
      match uu____227 with
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
    fun uu___113_240  ->
      match uu___113_240 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____249 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____249 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____255 = try_subst ts args in
               (match uu____255 with
                | FStar_Pervasives_Native.None  ->
                    let uu____260 =
                      let uu____261 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1 in
                      let uu____262 =
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu____263 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____261 uu____262 uu____263 in
                    failwith uu____260
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____267 -> FStar_Pervasives_Native.None)
      | uu____270 -> FStar_Pervasives_Native.None
let eff_leq:
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____279) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____280 -> false
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___114_288  ->
    match uu___114_288 with
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
        | uu____301 ->
            let uu____306 =
              let uu____307 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____307
                (eff_to_string f) (eff_to_string f') in
            failwith uu____306
let join_l:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun uu____337 =
  FStar_List.fold_right
    (fun uu____346  ->
       fun t  ->
         match uu____346 with
         | (uu____352,t0) ->
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
                | uu____439 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____471 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____478 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____478 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____488;
                     FStar_Extraction_ML_Syntax.loc = uu____489;_}
                   ->
                   let uu____510 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____510
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____526 = type_leq unfold_ty t2 t2' in
                        (if uu____526
                         then
                           let body1 =
                             let uu____537 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____537
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____542 =
                             let uu____545 =
                               let uu____546 =
                                 let uu____549 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____549 in
                               FStar_All.pipe_left uu____546
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu____545 in
                           (true, uu____542)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____578 =
                           let uu____585 =
                             let uu____588 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun _0_40  ->
                                  FStar_Pervasives_Native.Some _0_40)
                               uu____588 in
                           type_leq_c unfold_ty uu____585 t2 t2' in
                         match uu____578 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____612 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu____612
                               | uu____621 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____629 ->
                   let uu____632 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____632
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____668 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____668
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____684 = unfold_ty t in
                 match uu____684 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____698 = unfold_ty t' in
                     (match uu____698 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____720 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____720
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____737,uu____738) ->
              let uu____745 = unfold_ty t in
              (match uu____745 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____759 -> (false, FStar_Pervasives_Native.None))
          | (uu____764,FStar_Extraction_ML_Syntax.MLTY_Named uu____765) ->
              let uu____772 = unfold_ty t' in
              (match uu____772 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____786 -> (false, FStar_Pervasives_Native.None))
          | uu____791 -> (false, FStar_Pervasives_Native.None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____802 = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_All.pipe_right uu____802 FStar_Pervasives_Native.fst
let is_type_abstraction uu___115_844 =
  match uu___115_844 with
  | (FStar_Util.Inl uu____855,uu____856)::uu____857 -> true
  | uu____880 -> false
let is_xtuple:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____902  ->
    match uu____902 with
    | (ns,n1) ->
        let uu____917 =
          let uu____918 = FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_datacon_string uu____918 in
        if uu____917
        then
          let uu____921 =
            let uu____922 = FStar_Util.char_at n1 (Prims.parse_int "7") in
            FStar_Util.int_of_char uu____922 in
          FStar_Pervasives_Native.Some uu____921
        else FStar_Pervasives_Native.None
let resugar_exp:
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____934 = is_xtuple mlp in
        (match uu____934 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____938 -> e)
    | uu____941 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___116_949  ->
    match uu___116_949 with
    | f::uu____955 ->
        let uu____958 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____958 with
         | (ns,uu____968) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____979 -> failwith "impos"
let record_fields fs vs =
  FStar_List.map2
    (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e)) fs
    vs
let is_xtuple_ty:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____1032  ->
    match uu____1032 with
    | (ns,n1) ->
        let uu____1047 =
          let uu____1048 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_constructor_string uu____1048 in
        if uu____1047
        then
          let uu____1051 =
            let uu____1052 = FStar_Util.char_at n1 (Prims.parse_int "5") in
            FStar_Util.int_of_char uu____1052 in
          FStar_Pervasives_Native.Some uu____1051
        else FStar_Pervasives_Native.None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1064 = is_xtuple_ty mlp in
        (match uu____1064 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1068 -> t)
    | uu____1071 -> t
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____1075  ->
    let uu____1076 =
      let uu____1077 = FStar_Options.codegen () in
      FStar_Option.get uu____1077 in
    uu____1076 = "FSharp"
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____1088 = codegen_fsharp () in
    if uu____1088
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string
  =
  fun uu____1099  ->
    match uu____1099 with
    | (ns,n1) ->
        let uu____1112 = codegen_fsharp () in
        if uu____1112
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____1124 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____1124, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____1147 = unfold_ty t in
         match uu____1147 with
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
            let uu____1169 =
              let uu____1176 = eraseTypeDeep unfold_ty tyd in
              let uu____1180 = eraseTypeDeep unfold_ty tycd in
              (uu____1176, etag, uu____1180) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1169
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1191 = erasableType unfold_ty t in
          if uu____1191
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1196 =
               let uu____1203 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____1203, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1196)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1214 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1214
      | uu____1220 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____1223 =
    let uu____1226 =
      (mk_ty_fun ())
        [(("x", (Prims.parse_int "0")),
           FStar_Extraction_ML_Syntax.ml_bool_ty);
        (("y", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____1226 in
  FStar_All.pipe_left uu____1223
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
          let uu____1319 = conjoin x y in
          FStar_Pervasives_Native.Some uu____1319
let mlloc_of_range:
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____1330 = FStar_Range.file_of_range r in (line, uu____1330)
let rec argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1340,b) ->
        let uu____1342 = argTypes b in a :: uu____1342
    | uu____1345 -> []
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1363,b) ->
        let uu____1365 = uncurry_mlty_fun b in
        (match uu____1365 with | (args,res) -> ((a :: args), res))
    | uu____1386 -> ([], t)
type emb_decl =
  | Embed
  | Unembed
let uu___is_Embed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____1393 -> false
let uu___is_Unembed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____1398 -> false
let lid_to_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun l  ->
    let uu____1403 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
    FStar_Extraction_ML_Syntax.MLE_Name uu____1403
let lid_to_top_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun l  ->
    let uu____1408 =
      let uu____1409 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
      FStar_Extraction_ML_Syntax.MLE_Name uu____1409 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1408
let str_to_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  ->
    let uu____1414 = FStar_Ident.lid_of_str s in lid_to_name uu____1414
let str_to_top_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr =
  fun s  ->
    let uu____1419 = FStar_Ident.lid_of_str s in lid_to_top_name uu____1419
let fstar_tc_common_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_TypeChecker_Common." s)
let fstar_refl_basic_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Basic." s)
let fstar_refl_data_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Data." s)
let mk_embedding:
  emb_decl -> Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun m  ->
    fun s  ->
      match m with
      | Embed  -> fstar_refl_basic_prefix (Prims.strcat "embed_" s)
      | Unembed  -> fstar_refl_basic_prefix (Prims.strcat "unembed_" s)
let rec mk_tac_param_type:
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun t  ->
    let uu____1444 =
      let uu____1445 = FStar_Syntax_Subst.compress t in
      uu____1445.FStar_Syntax_Syntax.n in
    match uu____1444 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
        fstar_tc_common_prefix "t_int"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
        fstar_tc_common_prefix "t_bool"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
        fstar_tc_common_prefix "t_unit"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid ->
        fstar_tc_common_prefix "t_string"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1455 = FStar_Reflection_Data.fstar_refl_types_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1455 ->
        fstar_refl_data_prefix "t_binder"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1457 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1457 ->
        fstar_refl_data_prefix "t_term"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1459 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1459 ->
        fstar_refl_data_prefix "t_fv"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1461 = FStar_Reflection_Data.fstar_refl_syntax_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1461 ->
        fstar_refl_data_prefix "t_binders"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1463 =
          FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1463 ->
        fstar_refl_data_prefix "t_norm_step"
    | FStar_Syntax_Syntax.Tm_app (h,args) ->
        let uu____1494 =
          let uu____1495 = FStar_Syntax_Subst.compress h in
          uu____1495.FStar_Syntax_Syntax.n in
        (match uu____1494 with
         | FStar_Syntax_Syntax.Tm_uinst (h',uu____1501) ->
             let uu____1510 =
               let uu____1511 = FStar_Syntax_Subst.compress h' in
               uu____1511.FStar_Syntax_Syntax.n in
             (match uu____1510 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.list_lid
                  ->
                  let arg_term =
                    let uu____1522 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1522 in
                  let uu____1543 =
                    let uu____1550 =
                      let uu____1551 = fstar_tc_common_prefix "t_list_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1551 in
                    let uu____1552 =
                      let uu____1555 =
                        let uu____1558 = mk_tac_param_type arg_term in
                        [uu____1558] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1555 in
                    (uu____1550, uu____1552) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1543
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.option_lid
                  ->
                  let arg_term =
                    let uu____1567 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1567 in
                  let uu____1588 =
                    let uu____1595 =
                      let uu____1596 = fstar_tc_common_prefix "t_option_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1596 in
                    let uu____1597 =
                      let uu____1600 =
                        let uu____1603 = mk_tac_param_type arg_term in
                        [uu____1603] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1600 in
                    (uu____1595, uu____1597) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1588
              | uu____1606 ->
                  let uu____1607 =
                    let uu____1608 =
                      let uu____1609 = FStar_Syntax_Subst.compress h' in
                      FStar_Syntax_Print.term_to_string uu____1609 in
                    Prims.strcat
                      "Type term not defined for higher-order type "
                      uu____1608 in
                  failwith uu____1607)
         | uu____1610 -> failwith "Impossible")
    | uu____1611 ->
        let uu____1612 =
          let uu____1613 =
            let uu____1614 = FStar_Syntax_Subst.compress t in
            FStar_Syntax_Print.term_to_string uu____1614 in
          Prims.strcat "Type term not defined for " uu____1613 in
        failwith uu____1612
let rec mk_tac_embedding_path:
  emb_decl -> FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun m  ->
    fun t  ->
      let uu____1623 =
        let uu____1624 = FStar_Syntax_Subst.compress t in
        uu____1624.FStar_Syntax_Syntax.n in
      match uu____1623 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
          mk_embedding m "int"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
          mk_embedding m "bool"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
          mk_embedding m "unit"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid ->
          mk_embedding m "string"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1634 =
            FStar_Reflection_Data.fstar_refl_types_lid "binder" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1634 ->
          mk_embedding m "binder"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1636 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1636 ->
          mk_embedding m "term"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1638 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1638 ->
          mk_embedding m "fvar"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1640 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "binders" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1640 ->
          mk_embedding m "binders"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1642 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1642 ->
          mk_embedding m "norm_step"
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____1673 =
            let uu____1674 = FStar_Syntax_Subst.compress h in
            uu____1674.FStar_Syntax_Syntax.n in
          (match uu____1673 with
           | FStar_Syntax_Syntax.Tm_uinst (h',uu____1680) ->
               let uu____1689 =
                 let uu____1698 =
                   let uu____1699 = FStar_Syntax_Subst.compress h' in
                   uu____1699.FStar_Syntax_Syntax.n in
                 match uu____1698 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.list_lid
                     ->
                     let arg_term =
                       let uu____1718 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1718 in
                     let uu____1739 =
                       let uu____1742 = mk_tac_embedding_path m arg_term in
                       [uu____1742] in
                     let uu____1743 = mk_tac_param_type arg_term in
                     ("list", uu____1739, uu____1743)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.option_lid
                     ->
                     let arg_term =
                       let uu____1752 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1752 in
                     let uu____1773 =
                       let uu____1776 = mk_tac_embedding_path m arg_term in
                       [uu____1776] in
                     let uu____1777 = mk_tac_param_type arg_term in
                     ("option", uu____1773, uu____1777)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.tactic_lid
                     -> failwith "Embedding for tactics not defined"
                 | uu____1789 ->
                     let uu____1790 =
                       let uu____1791 =
                         let uu____1792 = FStar_Syntax_Subst.compress h' in
                         FStar_Syntax_Print.term_to_string uu____1792 in
                       Prims.strcat
                         "Embedding not defined for higher-order type "
                         uu____1791 in
                     failwith uu____1790 in
               (match uu____1689 with
                | (ht,hargs,type_arg) ->
                    let hargs1 =
                      match m with
                      | Embed  -> FStar_List.append hargs [type_arg]
                      | Unembed  -> hargs in
                    let uu____1813 =
                      let uu____1820 =
                        let uu____1821 = mk_embedding m ht in
                        FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top uu____1821 in
                      let uu____1822 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) hargs1 in
                      (uu____1820, uu____1822) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____1813)
           | uu____1827 -> failwith "Impossible")
      | uu____1828 ->
          let uu____1829 =
            let uu____1830 =
              let uu____1831 = FStar_Syntax_Subst.compress t in
              FStar_Syntax_Print.term_to_string uu____1831 in
            Prims.strcat "Embedding not defined for type " uu____1830 in
          failwith uu____1829
let mk_interpretation_fun tac_lid assm_lid t bs =
  let arg_types =
    FStar_List.map
      (fun x  -> (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort) bs in
  let arity = FStar_List.length bs in
  let h =
    let uu____1898 =
      let uu____1899 = FStar_Util.string_of_int arity in
      Prims.strcat "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
        uu____1899 in
    str_to_top_name uu____1898 in
  let tac_fun =
    let uu____1907 =
      let uu____1914 =
        let uu____1915 =
          let uu____1916 = FStar_Util.string_of_int arity in
          Prims.strcat "FStar_Tactics_Native.from_tactic_" uu____1916 in
        str_to_top_name uu____1915 in
      let uu____1923 =
        let uu____1926 = lid_to_top_name tac_lid in [uu____1926] in
      (uu____1914, uu____1923) in
    FStar_Extraction_ML_Syntax.MLE_App uu____1907 in
  let tac_lid_app =
    let uu____1930 =
      let uu____1937 = str_to_top_name "FStar_Ident.lid_of_str" in
      (uu____1937,
        [FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top assm_lid]) in
    FStar_Extraction_ML_Syntax.MLE_App uu____1930 in
  let args =
    let uu____1943 =
      let uu____1946 = str_to_name "ps" in [uu____1946; tac_fun] in
    let uu____1947 =
      let uu____1950 =
        FStar_List.map (mk_tac_embedding_path Unembed) arg_types in
      let uu____1953 =
        let uu____1956 = mk_tac_embedding_path Embed t in
        let uu____1957 =
          let uu____1960 = mk_tac_param_type t in
          let uu____1961 =
            let uu____1964 =
              let uu____1967 = str_to_name "args" in [uu____1967] in
            tac_lid_app :: uu____1964 in
          uu____1960 :: uu____1961 in
        uu____1956 :: uu____1957 in
      FStar_List.append uu____1950 uu____1953 in
    FStar_List.append uu____1943 uu____1947 in
  let app =
    let uu____1969 =
      let uu____1970 =
        let uu____1977 =
          FStar_List.map
            (FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.MLTY_Top) args in
        (h, uu____1977) in
      FStar_Extraction_ML_Syntax.MLE_App uu____1970 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1969 in
  FStar_Extraction_ML_Syntax.MLE_Fun
    ([(("ps", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.MLTY_Top);
     (("args", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.MLTY_Top)],
      app)