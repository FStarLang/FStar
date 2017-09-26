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
    | FStar_Const.Const_bytearray (bytes,uu____77) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____83) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____84 ->
        failwith "Unhandled constant: reify/reflect"
let mlconst_of_const':
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const c
      with
      | uu____99 ->
          let uu____100 =
            let uu____101 = FStar_Range.string_of_range p in
            let uu____102 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____101 uu____102 in
          failwith uu____100
let rec subst_aux:
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____124 =
            FStar_Util.find_opt
              (fun uu____138  ->
                 match uu____138 with | (y,uu____144) -> y = x) subst1 in
          (match uu____124 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____161 =
            let uu____168 = subst_aux subst1 t1 in
            let uu____169 = subst_aux subst1 t2 in (uu____168, f, uu____169) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____161
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____176 =
            let uu____183 = FStar_List.map (subst_aux subst1) args in
            (uu____183, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____176
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____191 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____191
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let try_subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun uu____204  ->
    fun args  ->
      match uu____204 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____215 =
               let uu____216 = FStar_List.zip formals args in
               subst_aux uu____216 t in
             FStar_Pervasives_Native.Some uu____215)
let subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun ts  ->
    fun args  ->
      let uu____235 = try_subst ts args in
      match uu____235 with
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
    fun uu___118_248  ->
      match uu___118_248 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____257 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____257 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____263 = try_subst ts args in
               (match uu____263 with
                | FStar_Pervasives_Native.None  ->
                    let uu____268 =
                      let uu____269 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1 in
                      let uu____270 =
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu____271 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____269 uu____270 uu____271 in
                    failwith uu____268
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____275 -> FStar_Pervasives_Native.None)
      | uu____278 -> FStar_Pervasives_Native.None
let eff_leq:
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____287) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____288 -> false
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___119_296  ->
    match uu___119_296 with
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
        | uu____309 ->
            let uu____314 =
              let uu____315 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____315
                (eff_to_string f) (eff_to_string f') in
            failwith uu____314
let join_l:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun:
  'Auu____334 .
    Prims.unit ->
      ('Auu____334,FStar_Extraction_ML_Syntax.mlty)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____345  ->
    FStar_List.fold_right
      (fun uu____354  ->
         fun t  ->
           match uu____354 with
           | (uu____360,t0) ->
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
                | uu____447 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____479 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____486 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____486 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____496;
                     FStar_Extraction_ML_Syntax.loc = uu____497;_}
                   ->
                   let uu____518 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____518
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____534 = type_leq unfold_ty t2 t2' in
                        (if uu____534
                         then
                           let body1 =
                             let uu____545 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____545
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____550 =
                             let uu____553 =
                               let uu____554 =
                                 let uu____557 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____557 in
                               FStar_All.pipe_left uu____554
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu____553 in
                           (true, uu____550)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____586 =
                           let uu____593 =
                             let uu____596 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun _0_42  ->
                                  FStar_Pervasives_Native.Some _0_42)
                               uu____596 in
                           type_leq_c unfold_ty uu____593 t2 t2' in
                         match uu____586 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____620 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu____620
                               | uu____629 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____637 ->
                   let uu____640 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____640
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____676 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____676
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____692 = unfold_ty t in
                 match uu____692 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____706 = unfold_ty t' in
                     (match uu____706 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____728 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____728
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____745,uu____746) ->
              let uu____753 = unfold_ty t in
              (match uu____753 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____767 -> (false, FStar_Pervasives_Native.None))
          | (uu____772,FStar_Extraction_ML_Syntax.MLTY_Named uu____773) ->
              let uu____780 = unfold_ty t' in
              (match uu____780 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____794 -> (false, FStar_Pervasives_Native.None))
          | uu____799 -> (false, FStar_Pervasives_Native.None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____810 = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_All.pipe_right uu____810 FStar_Pervasives_Native.fst
let is_type_abstraction:
  'Auu____836 'Auu____837 'Auu____838 .
    (('Auu____838,'Auu____837) FStar_Util.either,'Auu____836)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun uu___120_852  ->
    match uu___120_852 with
    | (FStar_Util.Inl uu____863,uu____864)::uu____865 -> true
    | uu____888 -> false
let is_xtuple:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____910  ->
    match uu____910 with
    | (ns,n1) ->
        let uu____925 =
          let uu____926 = FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_datacon_string uu____926 in
        if uu____925
        then
          let uu____929 =
            let uu____930 = FStar_Util.char_at n1 (Prims.parse_int "7") in
            FStar_Util.int_of_char uu____930 in
          FStar_Pervasives_Native.Some uu____929
        else FStar_Pervasives_Native.None
let resugar_exp:
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____954 = is_xtuple mlp in
        (match uu____954 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____958 -> e)
    | uu____961 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___121_969  ->
    match uu___121_969 with
    | f::uu____975 ->
        let uu____978 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____978 with
         | (ns,uu____988) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____999 -> failwith "impos"
let record_fields:
  'Auu____1010 .
    FStar_Ident.lident Prims.list ->
      'Auu____1010 Prims.list ->
        (Prims.string,'Auu____1010) FStar_Pervasives_Native.tuple2 Prims.list
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
  fun uu____1052  ->
    match uu____1052 with
    | (ns,n1) ->
        let uu____1067 =
          let uu____1068 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_constructor_string uu____1068 in
        if uu____1067
        then
          let uu____1071 =
            let uu____1072 = FStar_Util.char_at n1 (Prims.parse_int "5") in
            FStar_Util.int_of_char uu____1072 in
          FStar_Pervasives_Native.Some uu____1071
        else FStar_Pervasives_Native.None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1096 = is_xtuple_ty mlp in
        (match uu____1096 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1100 -> t)
    | uu____1103 -> t
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____1107  ->
    let uu____1108 =
      let uu____1109 = FStar_Options.codegen () in
      FStar_Option.get uu____1109 in
    uu____1108 = "FSharp"
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____1120 = codegen_fsharp () in
    if uu____1120
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string
  =
  fun uu____1131  ->
    match uu____1131 with
    | (ns,n1) ->
        let uu____1144 = codegen_fsharp () in
        if uu____1144
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____1156 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____1156, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____1179 = unfold_ty t in
         match uu____1179 with
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
            let uu____1201 =
              let uu____1208 = eraseTypeDeep unfold_ty tyd in
              let uu____1212 = eraseTypeDeep unfold_ty tycd in
              (uu____1208, etag, uu____1212) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1201
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1223 = erasableType unfold_ty t in
          if uu____1223
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1228 =
               let uu____1235 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____1235, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1228)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1246 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1246
      | uu____1252 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____1255 =
    let uu____1258 =
      (mk_ty_fun ())
        [(("x", (Prims.parse_int "0")),
           FStar_Extraction_ML_Syntax.ml_bool_ty);
        (("y", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____1258 in
  FStar_All.pipe_left uu____1255
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
          let uu____1351 = conjoin x y in
          FStar_Pervasives_Native.Some uu____1351
let mlloc_of_range:
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____1362 = FStar_Range.file_of_range r in (line, uu____1362)
let rec doms_and_cod:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1380,b) ->
        let uu____1382 = doms_and_cod b in
        (match uu____1382 with | (ds,c) -> ((a :: ds), c))
    | uu____1403 -> ([], t)
let argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    let uu____1414 = doms_and_cod t in FStar_Pervasives_Native.fst uu____1414
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1440,b) ->
        let uu____1442 = uncurry_mlty_fun b in
        (match uu____1442 with | (args,res) -> ((a :: args), res))
    | uu____1463 -> ([], t)
exception CallNotImplemented
let uu___is_CallNotImplemented: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | CallNotImplemented  -> true | uu____1470 -> false
let not_implemented_warning: Prims.string -> Prims.unit =
  fun t  ->
    let uu____1475 =
      FStar_Util.format1 ". Tactic %s will not run natively.\n" t in
    FStar_All.pipe_right uu____1475 FStar_Util.print_warning
type emb_decl =
  | Embed
  | Unembed[@@deriving show]
let uu___is_Embed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____1480 -> false
let uu___is_Unembed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____1485 -> false
let lid_to_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun l  ->
    let uu____1490 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
    FStar_Extraction_ML_Syntax.MLE_Name uu____1490
let lid_to_top_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun l  ->
    let uu____1495 =
      let uu____1496 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
      FStar_Extraction_ML_Syntax.MLE_Name uu____1496 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1495
let str_to_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  ->
    let uu____1501 = FStar_Ident.lid_of_str s in lid_to_name uu____1501
let str_to_top_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr =
  fun s  ->
    let uu____1506 = FStar_Ident.lid_of_str s in lid_to_top_name uu____1506
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
      let uu____1553 =
        let uu____1554 =
          let uu____1561 =
            str_to_top_name "FStar_Tactics_Interpreter.reify_tactic" in
          let uu____1562 =
            let uu____1565 = str_to_top_name tac_arg in [uu____1565] in
          (uu____1561, uu____1562) in
        FStar_Extraction_ML_Syntax.MLE_App uu____1554 in
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1553 in
    let from_tac =
      let uu____1569 =
        let uu____1570 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Builtins.from_tac_" uu____1570 in
      str_to_top_name uu____1569 in
    let unembed_tactic =
      let uu____1572 =
        let uu____1573 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Interpreter.unembed_tactic_" uu____1573 in
      str_to_top_name uu____1572 in
    let app =
      match FStar_List.length args with
      | _0_43 when _0_43 = (Prims.parse_int "1") ->
          let uu____1575 =
            let uu____1582 =
              let uu____1585 =
                let uu____1586 =
                  let uu____1587 =
                    let uu____1594 =
                      let uu____1597 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) args in
                      FStar_List.append uu____1597 [reify_tactic] in
                    (unembed_tactic, uu____1594) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1587 in
                FStar_Extraction_ML_Syntax.with_ty
                  FStar_Extraction_ML_Syntax.MLTY_Top uu____1586 in
              [uu____1585] in
            (from_tac, uu____1582) in
          FStar_Extraction_ML_Syntax.MLE_App uu____1575
      | n1 ->
          ((let uu____1606 =
              let uu____1607 =
                let uu____1610 = FStar_Util.string_of_int n1 in [uu____1610] in
              FStar_Util.format
                "Unembedding not defined for tactics of %d arguments"
                uu____1607 in
            FStar_Util.print_warning uu____1606);
           FStar_Exn.raise CallNotImplemented) in
    FStar_Extraction_ML_Syntax.MLE_Fun
      ([((tac_arg, (Prims.parse_int "0")),
          FStar_Extraction_ML_Syntax.MLTY_Top);
       (("()", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.MLTY_Top)],
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top app))
let rec mk_tac_param_type:
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun t  ->
    let uu____1663 =
      let uu____1664 = FStar_Syntax_Subst.compress t in
      uu____1664.FStar_Syntax_Syntax.n in
    match uu____1663 with
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
        let uu____1672 = FStar_Reflection_Data.fstar_refl_types_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1672 ->
        fstar_refl_data_prefix "t_binder"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1674 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1674 ->
        fstar_refl_data_prefix "t_term"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1676 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1676 ->
        fstar_refl_data_prefix "t_fv"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1678 = FStar_Reflection_Data.fstar_refl_syntax_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1678 ->
        fstar_refl_data_prefix "t_binders"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1680 =
          FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1680 ->
        fstar_refl_data_prefix "t_norm_step"
    | FStar_Syntax_Syntax.Tm_app (h,args) ->
        let uu____1703 =
          let uu____1704 = FStar_Syntax_Subst.compress h in
          uu____1704.FStar_Syntax_Syntax.n in
        (match uu____1703 with
         | FStar_Syntax_Syntax.Tm_uinst (h',uu____1708) ->
             let uu____1713 =
               let uu____1714 = FStar_Syntax_Subst.compress h' in
               uu____1714.FStar_Syntax_Syntax.n in
             (match uu____1713 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.list_lid
                  ->
                  let arg_term =
                    let uu____1721 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1721 in
                  let uu____1736 =
                    let uu____1743 =
                      let uu____1744 = fstar_tc_common_prefix "t_list_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1744 in
                    let uu____1745 =
                      let uu____1748 =
                        let uu____1751 = mk_tac_param_type arg_term in
                        [uu____1751] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1748 in
                    (uu____1743, uu____1745) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1736
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.option_lid
                  ->
                  let arg_term =
                    let uu____1758 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1758 in
                  let uu____1773 =
                    let uu____1780 =
                      let uu____1781 = fstar_tc_common_prefix "t_option_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1781 in
                    let uu____1782 =
                      let uu____1785 =
                        let uu____1788 = mk_tac_param_type arg_term in
                        [uu____1788] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1785 in
                    (uu____1780, uu____1782) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1773
              | uu____1791 ->
                  ((let uu____1793 =
                      let uu____1794 =
                        let uu____1795 = FStar_Syntax_Subst.compress h' in
                        FStar_Syntax_Print.term_to_string uu____1795 in
                      Prims.strcat
                        "Type term not defined for higher-order type "
                        uu____1794 in
                    FStar_Util.print_warning uu____1793);
                   FStar_Exn.raise CallNotImplemented))
         | uu____1796 ->
             (FStar_Util.print_warning "Impossible";
              FStar_Exn.raise CallNotImplemented))
    | uu____1798 ->
        ((let uu____1800 =
            let uu____1801 =
              let uu____1802 = FStar_Syntax_Subst.compress t in
              FStar_Syntax_Print.term_to_string uu____1802 in
            Prims.strcat "Type term not defined for " uu____1801 in
          FStar_Util.print_warning uu____1800);
         FStar_Exn.raise CallNotImplemented)
let rec mk_tac_embedding_path:
  emb_decl -> FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun m  ->
    fun t  ->
      let uu____1811 =
        let uu____1812 = FStar_Syntax_Subst.compress t in
        uu____1812.FStar_Syntax_Syntax.n in
      match uu____1811 with
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
          let uu____1820 =
            FStar_Reflection_Data.fstar_refl_types_lid "binder" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1820 ->
          mk_embedding m "binder"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1822 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1822 ->
          mk_embedding m "term"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1824 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1824 ->
          mk_embedding m "fvar"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1826 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "binders" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1826 ->
          mk_embedding m "binders"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1828 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1828 ->
          mk_embedding m "norm_step"
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____1851 =
            let uu____1852 = FStar_Syntax_Subst.compress h in
            uu____1852.FStar_Syntax_Syntax.n in
          (match uu____1851 with
           | FStar_Syntax_Syntax.Tm_uinst (h',uu____1856) ->
               let uu____1861 =
                 let uu____1872 =
                   let uu____1873 = FStar_Syntax_Subst.compress h' in
                   uu____1873.FStar_Syntax_Syntax.n in
                 match uu____1872 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.list_lid
                     ->
                     let arg_term =
                       let uu____1890 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1890 in
                     let uu____1905 =
                       let uu____1908 = mk_tac_embedding_path m arg_term in
                       [uu____1908] in
                     let uu____1909 = mk_tac_param_type arg_term in
                     ("list", uu____1905, uu____1909, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.option_lid
                     ->
                     let arg_term =
                       let uu____1916 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1916 in
                     let uu____1931 =
                       let uu____1934 = mk_tac_embedding_path m arg_term in
                       [uu____1934] in
                     let uu____1935 = mk_tac_param_type arg_term in
                     ("option", uu____1931, uu____1935, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.tactic_lid
                     ->
                     let arg_term =
                       let uu____1942 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1942 in
                     let uu____1957 =
                       let uu____1960 = mk_tac_embedding_path m arg_term in
                       [uu____1960] in
                     let uu____1961 = mk_tac_param_type arg_term in
                     ("list", uu____1957, uu____1961, true)
                 | uu____1964 ->
                     ((let uu____1966 =
                         let uu____1967 =
                           let uu____1968 = FStar_Syntax_Subst.compress h' in
                           FStar_Syntax_Print.term_to_string uu____1968 in
                         Prims.strcat
                           "Embedding not defined for higher-order type "
                           uu____1967 in
                       FStar_Util.print_warning uu____1966);
                      FStar_Exn.raise CallNotImplemented) in
               (match uu____1861 with
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
                      (let uu____1994 =
                         let uu____2001 =
                           let uu____2002 = mk_basic_embedding m ht in
                           FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top uu____2002 in
                         let uu____2003 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top) hargs1 in
                         (uu____2001, uu____2003) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____1994))
           | uu____2008 ->
               (FStar_Util.print_warning "Impossible";
                FStar_Exn.raise CallNotImplemented))
      | uu____2010 ->
          ((let uu____2012 =
              let uu____2013 =
                let uu____2014 = FStar_Syntax_Subst.compress t in
                FStar_Syntax_Print.term_to_string uu____2014 in
              Prims.strcat "Embedding not defined for type " uu____2013 in
            FStar_Util.print_warning uu____2012);
           FStar_Exn.raise CallNotImplemented)
let mk_interpretation_fun:
  'Auu____2025 .
    FStar_Ident.lident ->
      FStar_Extraction_ML_Syntax.mlexpr' ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,'Auu____2025)
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
              let uu____2092 =
                let uu____2093 = FStar_Util.string_of_int arity in
                Prims.strcat
                  "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                  uu____2093 in
              str_to_top_name uu____2092 in
            let tac_fun =
              let uu____2101 =
                let uu____2108 =
                  let uu____2109 =
                    let uu____2110 = FStar_Util.string_of_int arity in
                    Prims.strcat "FStar_Tactics_Native.from_tactic_"
                      uu____2110 in
                  str_to_top_name uu____2109 in
                let uu____2117 =
                  let uu____2120 = lid_to_top_name tac_lid in [uu____2120] in
                (uu____2108, uu____2117) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2101 in
            let tac_lid_app =
              let uu____2124 =
                let uu____2131 = str_to_top_name "FStar_Ident.lid_of_str" in
                (uu____2131,
                  [FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.MLTY_Top assm_lid]) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2124 in
            let args =
              let uu____2137 =
                let uu____2140 = str_to_name "ps" in [uu____2140; tac_fun] in
              let uu____2141 =
                let uu____2144 =
                  FStar_List.map (mk_tac_embedding_path Unembed) arg_types in
                let uu____2147 =
                  let uu____2150 = mk_tac_embedding_path Embed t in
                  let uu____2151 =
                    let uu____2154 = mk_tac_param_type t in
                    let uu____2155 =
                      let uu____2158 =
                        let uu____2161 = str_to_name "args" in [uu____2161] in
                      tac_lid_app :: uu____2158 in
                    uu____2154 :: uu____2155 in
                  uu____2150 :: uu____2151 in
                FStar_List.append uu____2144 uu____2147 in
              FStar_List.append uu____2137 uu____2141 in
            let app =
              let uu____2163 =
                let uu____2164 =
                  let uu____2171 =
                    FStar_List.map
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top) args in
                  (h, uu____2171) in
                FStar_Extraction_ML_Syntax.MLE_App uu____2164 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2163 in
            FStar_Pervasives_Native.Some
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([(("ps", (Prims.parse_int "0")),
                     FStar_Extraction_ML_Syntax.MLTY_Top);
                  (("args", (Prims.parse_int "0")),
                    FStar_Extraction_ML_Syntax.MLTY_Top)], app))
          with
          | CallNotImplemented  ->
              ((let uu____2224 = FStar_Ident.string_of_lid tac_lid in
                not_implemented_warning uu____2224);
               FStar_Pervasives_Native.None)