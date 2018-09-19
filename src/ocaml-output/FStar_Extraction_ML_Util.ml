open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____5  ->
    let uu____6 = FStar_Options.codegen ()  in
    uu____6 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
let pruneNones :
  'a . 'a FStar_Pervasives_Native.option Prims.list -> 'a Prims.list =
  fun l  ->
    FStar_List.fold_right
      (fun x  ->
         fun ll  ->
           match x with
           | FStar_Pervasives_Native.Some xs -> xs :: ll
           | FStar_Pervasives_Native.None  -> ll) l []
  
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
  fun sctt  ->
    match sctt with
    | FStar_Const.Const_effect  -> failwith "Unsupported constant"
    | FStar_Const.Const_range uu____56 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____82) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____88) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____89 ->
        failwith "Unhandled constant: reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try (fun uu___274_101  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___273_104 ->
          let uu____105 =
            let uu____106 = FStar_Range.string_of_range p  in
            let uu____107 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____106 uu____107
             in
          failwith uu____105
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____119 =
        let uu____120 =
          let uu____121 =
            let uu____132 = FStar_Util.string_of_int i  in
            (uu____132, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____121  in
        FStar_All.pipe_right uu____120
          (fun _0_1  -> FStar_Extraction_ML_Syntax.MLE_Const _0_1)
         in
      FStar_All.pipe_right uu____119
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____149 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_2  -> FStar_Extraction_ML_Syntax.MLE_Const _0_2)
         in
      FStar_All.pipe_right uu____149
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____150 =
      let uu____157 =
        let uu____160 =
          let uu____161 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____161 cstr  in
        let uu____162 =
          let uu____165 =
            let uu____166 =
              let uu____167 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____167 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____166 cint  in
          let uu____168 =
            let uu____171 =
              let uu____172 =
                let uu____173 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____173 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____172 cint  in
            let uu____174 =
              let uu____177 =
                let uu____178 =
                  let uu____179 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____179 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____178 cint  in
              let uu____180 =
                let uu____183 =
                  let uu____184 =
                    let uu____185 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____185 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____184 cint  in
                [uu____183]  in
              uu____177 :: uu____180  in
            uu____171 :: uu____174  in
          uu____165 :: uu____168  in
        uu____160 :: uu____162  in
      (mk_range_mle, uu____157)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____150
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____199 ->
          let uu____200 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____200
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____224 =
            FStar_Util.find_opt
              (fun uu____238  ->
                 match uu____238 with | (y,uu____244) -> y = x) subst1
             in
          (match uu____224 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____261 =
            let uu____268 = subst_aux subst1 t1  in
            let uu____269 = subst_aux subst1 t2  in (uu____268, f, uu____269)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____261
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____276 =
            let uu____283 = FStar_List.map (subst_aux subst1) args  in
            (uu____283, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____276
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____291 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____291
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____306  ->
    fun args  ->
      match uu____306 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____317 =
               let uu____318 = FStar_List.zip formals args  in
               subst_aux uu____318 t  in
             FStar_Pervasives_Native.Some uu____317)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____347 = try_subst ts args  in
      match uu____347 with
      | FStar_Pervasives_Native.None  ->
          failwith
            "Substitution must be fully applied (see GitHub issue #490)"
      | FStar_Pervasives_Native.Some t -> t
  
let (udelta_unfold :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun uu___266_362  ->
      match uu___266_362 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____371 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____371 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____377 = try_subst ts args  in
               (match uu____377 with
                | FStar_Pervasives_Native.None  ->
                    let uu____382 =
                      let uu____383 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____384 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____385 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____383 uu____384 uu____385
                       in
                    failwith uu____382
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____389 -> FStar_Pervasives_Native.None)
      | uu____392 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____403) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____404 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___267_413  ->
    match uu___267_413 with
    | FStar_Extraction_ML_Syntax.E_PURE  -> "Pure"
    | FStar_Extraction_ML_Syntax.E_GHOST  -> "Ghost"
    | FStar_Extraction_ML_Syntax.E_IMPURE  -> "Impure"
  
let (join :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.e_tag -> FStar_Extraction_ML_Syntax.e_tag)
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
        | uu____429 ->
            let uu____434 =
              let uu____435 = FStar_Range.string_of_range r  in
              let uu____436 = eff_to_string f  in
              let uu____437 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____435
                uu____436 uu____437
               in
            failwith uu____434
  
let (join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
  
let (mk_ty_fun :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  FStar_List.fold_right
    (fun uu____474  ->
       fun t  ->
         match uu____474 with
         | (uu____480,t0) ->
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
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2)
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
                | uu____589 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____621 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____628 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____628 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____638;
                     FStar_Extraction_ML_Syntax.loc = uu____639;_}
                   ->
                   let uu____660 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____660
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____676 = type_leq unfold_ty t2 t2'  in
                        (if uu____676
                         then
                           let body1 =
                             let uu____687 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____687
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____692 =
                             let uu____695 =
                               let uu____696 =
                                 let uu____701 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____701
                                  in
                               FStar_All.pipe_left uu____696
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____695  in
                           (true, uu____692)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____730 =
                           let uu____737 =
                             let uu____740 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_3  ->
                                  FStar_Pervasives_Native.Some _0_3)
                               uu____740
                              in
                           type_leq_c unfold_ty uu____737 t2 t2'  in
                         match uu____730 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____764 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____764
                               | uu____773 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____781 ->
                   let uu____784 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____784
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____820 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____820
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____836 = unfold_ty t  in
                 match uu____836 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____850 = unfold_ty t'  in
                     (match uu____850 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____872 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____872
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____889,uu____890) ->
              let uu____897 = unfold_ty t  in
              (match uu____897 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____911 -> (false, FStar_Pervasives_Native.None))
          | (uu____916,FStar_Extraction_ML_Syntax.MLTY_Named uu____917) ->
              let uu____924 = unfold_ty t'  in
              (match uu____924 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____938 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____945 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____957 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____957 FStar_Pervasives_Native.fst

let is_type_abstraction :
  'a 'b 'c .
    (('a,'b) FStar_Util.either,'c) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.bool
  =
  fun uu___268_1000  ->
    match uu___268_1000 with
    | (FStar_Util.Inl uu____1011,uu____1012)::uu____1013 -> true
    | uu____1036 -> false
  
let (is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1059  ->
    match uu____1059 with
    | (ns,n1) ->
        let uu____1074 =
          let uu____1075 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____1075  in
        if uu____1074
        then
          let uu____1078 =
            let uu____1079 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____1079  in
          FStar_Pervasives_Native.Some uu____1078
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1093 = is_xtuple mlp  in
        (match uu____1093 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1097 -> e)
    | uu____1100 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___269_1109  ->
    match uu___269_1109 with
    | f::uu____1115 ->
        let uu____1118 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1118 with
         | (ns,uu____1128) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1139 -> failwith "impos"
  
let record_fields :
  'a .
    FStar_Ident.lident Prims.list ->
      'a Prims.list ->
        (Prims.string,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2
        (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e))
        fs vs
  
let (is_xtuple_ty :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1195  ->
    match uu____1195 with
    | (ns,n1) ->
        let uu____1210 =
          let uu____1211 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1211  in
        if uu____1210
        then
          let uu____1214 =
            let uu____1215 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1215  in
          FStar_Pervasives_Native.Some uu____1214
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1229 = is_xtuple_ty mlp  in
        (match uu____1229 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1233 -> t)
    | uu____1236 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1246 = codegen_fsharp ()  in
    if uu____1246
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1258  ->
    match uu____1258 with
    | (ns,n1) ->
        let uu____1271 = codegen_fsharp ()  in
        if uu____1271
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____1284 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1284, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1310 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1310
      then true
      else
        (let uu____1312 = unfold_ty t  in
         match uu____1312 with
         | FStar_Pervasives_Native.Some t1 -> erasableType unfold_ty t1
         | FStar_Pervasives_Native.None  -> false)
  
let rec (eraseTypeDeep :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun unfold_ty  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Fun (tyd,etag,tycd) ->
          if etag = FStar_Extraction_ML_Syntax.E_PURE
          then
            let uu____1338 =
              let uu____1345 = eraseTypeDeep unfold_ty tyd  in
              let uu____1349 = eraseTypeDeep unfold_ty tycd  in
              (uu____1345, etag, uu____1349)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1338
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1360 = erasableType unfold_ty t  in
          if uu____1360
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1365 =
               let uu____1372 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1372, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1365)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1383 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1383
      | uu____1389 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1392 =
    let uu____1397 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1397  in
  FStar_All.pipe_left uu____1392
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_AmpAmp"))
  
let (conjoin :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun e1  ->
    fun e2  ->
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_bool_ty)
        (FStar_Extraction_ML_Syntax.MLE_App (prims_op_amp_amp, [e1; e2]))
  
let (conjoin_opt :
  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option)
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
          let uu____1470 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1470
  
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1482 = FStar_Range.file_of_range r  in (line, uu____1482)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1501,b) ->
        let uu____1503 = doms_and_cod b  in
        (match uu____1503 with | (ds,c) -> ((a :: ds), c))
    | uu____1524 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1536 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1536
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1563,b) ->
        let uu____1565 = uncurry_mlty_fun b  in
        (match uu____1565 with | (args,res) -> ((a :: args), res))
    | uu____1586 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____1598 -> true
    | uu____1599 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____1606 -> uu____1606
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1622 =
          let uu____1627 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1627)  in
        FStar_Errors.log_issue r uu____1622
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____1633 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____1639 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____1645 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____1651 -> false
  
type wrapped_term =
  (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlexpr,
    Prims.int,Prims.bool) FStar_Pervasives_Native.tuple4
let (interpret_plugin_as_term_fun :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ ->
        Prims.int FStar_Pervasives_Native.option ->
          FStar_Extraction_ML_Syntax.mlexpr' ->
            (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlexpr,
              Prims.int,Prims.bool) FStar_Pervasives_Native.tuple4
              FStar_Pervasives_Native.option)
  =
  fun tcenv  ->
    fun fv  ->
      fun t  ->
        fun arity_opt  ->
          fun ml_fv  ->
            let fv_lid1 =
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
            let t1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.EraseUniverses;
                FStar_TypeChecker_Env.AllowUnboundUniverses;
                FStar_TypeChecker_Env.UnfoldUntil
                  FStar_Syntax_Syntax.delta_constant] tcenv t
               in
            let w =
              FStar_Extraction_ML_Syntax.with_ty
                FStar_Extraction_ML_Syntax.MLTY_Top
               in
            let lid_to_name l =
              let uu____1714 =
                let uu____1715 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____1715  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1714
               in
            let lid_to_top_name l =
              let uu____1722 =
                let uu____1723 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____1723  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1722
               in
            let str_to_name s =
              let uu____1730 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____1730  in
            let str_to_top_name s =
              let uu____1737 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____1737  in
            let fstar_tc_nbe_prefix s =
              str_to_name (Prims.strcat "FStar_TypeChecker_NBETerm." s)  in
            let fstar_syn_emb_prefix s =
              str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)  in
            let fstar_refl_emb_prefix s =
              str_to_name (Prims.strcat "FStar_Reflection_Embeddings." s)  in
            let fstar_refl_nbeemb_prefix s =
              str_to_name (Prims.strcat "FStar_Reflection_NBEEmbeddings." s)
               in
            let fv_lid_embedded =
              let uu____1763 =
                let uu____1764 =
                  let uu____1771 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____1772 =
                    let uu____1775 =
                      let uu____1776 =
                        let uu____1777 =
                          let uu____1778 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____1778
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____1777  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1776
                       in
                    [uu____1775]  in
                  (uu____1771, uu____1772)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____1764  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1763
               in
            let emb_prefix uu___270_1791 =
              match uu___270_1791 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____1801 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____1808 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.strcat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____1831 =
                let uu____1832 = FStar_Util.string_of_int arity  in
                Prims.strcat "arrow_as_prim_step_" uu____1832  in
              emb_prefix l uu____1831  in
            let mk_any_embedding l s =
              let uu____1844 =
                let uu____1845 =
                  let uu____1852 = emb_prefix l "mk_any_emb"  in
                  let uu____1853 =
                    let uu____1856 = str_to_name s  in [uu____1856]  in
                  (uu____1852, uu____1853)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____1845  in
              FStar_All.pipe_left w uu____1844  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____1900 =
                let uu____1901 =
                  let uu____1908 = emb_prefix l "e_arrow"  in
                  (uu____1908, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____1901  in
              FStar_All.pipe_left w uu____1900  in
            let known_type_constructors =
              let term_cs =
                let uu____1941 =
                  let uu____1954 =
                    let uu____1967 =
                      let uu____1980 =
                        let uu____1993 =
                          let uu____2006 =
                            let uu____2019 =
                              let uu____2032 =
                                let uu____2043 =
                                  let uu____2050 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____2050, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____2043, Syntax_term)  in
                              let uu____2057 =
                                let uu____2070 =
                                  let uu____2081 =
                                    let uu____2088 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____2088, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____2081, Refl_emb)  in
                                let uu____2095 =
                                  let uu____2108 =
                                    let uu____2119 =
                                      let uu____2126 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____2126, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____2119, Refl_emb)  in
                                  let uu____2133 =
                                    let uu____2146 =
                                      let uu____2157 =
                                        let uu____2164 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____2164, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____2157, Refl_emb)  in
                                    let uu____2171 =
                                      let uu____2184 =
                                        let uu____2195 =
                                          let uu____2202 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____2202, (Prims.parse_int "0"),
                                            "binders")
                                           in
                                        (uu____2195, Refl_emb)  in
                                      let uu____2209 =
                                        let uu____2222 =
                                          let uu____2233 =
                                            let uu____2240 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____2240,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____2233, Refl_emb)  in
                                        [uu____2222]  in
                                      uu____2184 :: uu____2209  in
                                    uu____2146 :: uu____2171  in
                                  uu____2108 :: uu____2133  in
                                uu____2070 :: uu____2095  in
                              uu____2032 :: uu____2057  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____2019
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____2006
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____1993
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____1980
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____1967
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____1954
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____1941
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___271_2464  ->
                     match uu___271_2464 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____2523 -> failwith "Impossible") term_cs
                 in
              fun uu___272_2544  ->
                match uu___272_2544 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____2557 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____2589  ->
                   match uu____2589 with
                   | ((x,args,uu____2602),uu____2603) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____2624 =
              match uu____2624 with
              | (bv',uu____2630) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____2660 =
                let uu____2661 = FStar_Syntax_Subst.compress t3  in
                uu____2661.FStar_Syntax_Syntax.n  in
              match uu____2660 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____2669 =
                    let uu____2670 =
                      let uu____2675 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____2675  in
                    FStar_Pervasives_Native.snd uu____2670  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____2669
              | FStar_Syntax_Syntax.Tm_refine (x,uu____2691) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____2697,uu____2698) ->
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____2771 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____2771 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____2793 =
                           let uu____2794 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____2794  in
                         uu____2793.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____2812 = mk_embedding l env t0  in
                       let uu____2813 = mk_embedding l env t11  in
                       emb_arrow l uu____2812 uu____2813)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____2884 =
                      let uu____2891 =
                        let uu____2892 =
                          let uu____2907 = FStar_Syntax_Syntax.mk_Total tail1
                             in
                          ([b], uu____2907)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____2892  in
                      FStar_Syntax_Syntax.mk uu____2891  in
                    uu____2884 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____2935 ->
                  let uu____2936 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____2936 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____2988 =
                         let uu____2989 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____2989.FStar_Syntax_Syntax.n  in
                       (match uu____2988 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3019  ->
                                      match uu____3019 with
                                      | (t4,uu____3027) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3033 =
                              let uu____3044 =
                                FStar_Util.find_opt
                                  (fun uu____3072  ->
                                     match uu____3072 with
                                     | ((x,uu____3084,uu____3085),uu____3086)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3044 FStar_Util.must
                               in
                            (match uu____3033 with
                             | ((uu____3125,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _0_4 when _0_4 = (Prims.parse_int "0") ->
                                      head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____3139 ->
                            let uu____3140 =
                              let uu____3141 =
                                let uu____3142 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.strcat
                                  "Embedding not defined for type "
                                  uu____3142
                                 in
                              NoTacticEmbedding uu____3141  in
                            FStar_Exn.raise uu____3140))
              | FStar_Syntax_Syntax.Tm_uinst uu____3143 ->
                  let uu____3150 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3150 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3202 =
                         let uu____3203 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____3203.FStar_Syntax_Syntax.n  in
                       (match uu____3202 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3233  ->
                                      match uu____3233 with
                                      | (t4,uu____3241) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3247 =
                              let uu____3258 =
                                FStar_Util.find_opt
                                  (fun uu____3286  ->
                                     match uu____3286 with
                                     | ((x,uu____3298,uu____3299),uu____3300)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3258 FStar_Util.must
                               in
                            (match uu____3247 with
                             | ((uu____3339,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _0_5 when _0_5 = (Prims.parse_int "0") ->
                                      head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____3353 ->
                            let uu____3354 =
                              let uu____3355 =
                                let uu____3356 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.strcat
                                  "Embedding not defined for type "
                                  uu____3356
                                 in
                              NoTacticEmbedding uu____3355  in
                            FStar_Exn.raise uu____3354))
              | FStar_Syntax_Syntax.Tm_app uu____3357 ->
                  let uu____3374 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3374 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3426 =
                         let uu____3427 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____3427.FStar_Syntax_Syntax.n  in
                       (match uu____3426 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3457  ->
                                      match uu____3457 with
                                      | (t4,uu____3465) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3471 =
                              let uu____3482 =
                                FStar_Util.find_opt
                                  (fun uu____3510  ->
                                     match uu____3510 with
                                     | ((x,uu____3522,uu____3523),uu____3524)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3482 FStar_Util.must
                               in
                            (match uu____3471 with
                             | ((uu____3563,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _0_6 when _0_6 = (Prims.parse_int "0") ->
                                      head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____3577 ->
                            let uu____3578 =
                              let uu____3579 =
                                let uu____3580 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.strcat
                                  "Embedding not defined for type "
                                  uu____3580
                                 in
                              NoTacticEmbedding uu____3579  in
                            FStar_Exn.raise uu____3578))
              | uu____3581 ->
                  let uu____3582 =
                    let uu____3583 =
                      let uu____3584 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.strcat "Embedding not defined for type "
                        uu____3584
                       in
                    NoTacticEmbedding uu____3583  in
                  FStar_Exn.raise uu____3582
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____3601 =
                      let uu____3602 =
                        let uu____3609 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____3610 =
                          let uu____3613 =
                            let uu____3614 =
                              let uu____3615 =
                                let uu____3616 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____3616
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____3615
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____3614
                             in
                          let uu____3617 =
                            let uu____3620 =
                              let uu____3621 =
                                let uu____3622 =
                                  let uu____3623 =
                                    let uu____3630 =
                                      let uu____3633 = str_to_name "args"  in
                                      [uu____3633]  in
                                    (body, uu____3630)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3623
                                   in
                                FStar_All.pipe_left w uu____3622  in
                              mk_lam "_" uu____3621  in
                            [uu____3620]  in
                          uu____3613 :: uu____3617  in
                        (uu____3609, uu____3610)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____3602  in
                    FStar_All.pipe_left w uu____3601  in
                  mk_lam "args" body1
              | uu____3638 ->
                  let args_tail =
                    FStar_Extraction_ML_Syntax.MLP_Var "args_tail"  in
                  let mk_cons hd_pat tail_pat =
                    FStar_Extraction_ML_Syntax.MLP_CTor
                      ((["Prims"], "Cons"), [hd_pat; tail_pat])
                     in
                  let fst_pat v1 =
                    FStar_Extraction_ML_Syntax.MLP_Tuple
                      [FStar_Extraction_ML_Syntax.MLP_Var v1;
                      FStar_Extraction_ML_Syntax.MLP_Wild]
                     in
                  let pattern =
                    FStar_List.fold_right
                      (fun hd_var  -> mk_cons (fst_pat hd_var)) tvar_names
                      args_tail
                     in
                  let branch1 =
                    let uu____3675 =
                      let uu____3676 =
                        let uu____3677 =
                          let uu____3684 =
                            let uu____3687 = str_to_name "args"  in
                            [uu____3687]  in
                          (body, uu____3684)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____3677  in
                      FStar_All.pipe_left w uu____3676  in
                    (pattern, FStar_Pervasives_Native.None, uu____3675)  in
                  let default_branch =
                    let uu____3701 =
                      let uu____3702 =
                        let uu____3703 =
                          let uu____3710 = str_to_name "failwith"  in
                          let uu____3711 =
                            let uu____3714 =
                              let uu____3715 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____3715  in
                            [uu____3714]  in
                          (uu____3710, uu____3711)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____3703  in
                      FStar_All.pipe_left w uu____3702  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____3701)
                     in
                  let body1 =
                    let uu____3721 =
                      let uu____3722 =
                        let uu____3737 = str_to_name "args"  in
                        (uu____3737, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____3722  in
                    FStar_All.pipe_left w uu____3721  in
                  let body2 =
                    let uu____3773 =
                      let uu____3774 =
                        let uu____3781 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____3782 =
                          let uu____3785 =
                            let uu____3786 =
                              let uu____3787 =
                                let uu____3788 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____3788
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____3787
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____3786
                             in
                          let uu____3789 =
                            let uu____3792 = mk_lam "_" body1  in
                            [uu____3792]  in
                          uu____3785 :: uu____3789  in
                        (uu____3781, uu____3782)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____3774  in
                    FStar_All.pipe_left w uu____3773  in
                  mk_lam "args" body2
               in
            let uu____3795 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____3795 with
            | (bs,c) ->
                let uu____3828 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____3922 = FStar_Util.first_N n1 bs  in
                           match uu____3922 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____4000 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____4000
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____4015 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____4016 = FStar_Util.string_of_int n1  in
                             let uu____4017 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____4015 uu____4016 uu____4017
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____3828 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____4072 =
                       let uu____4093 =
                         FStar_Util.prefix_until
                           (fun uu____4135  ->
                              match uu____4135 with
                              | (b,uu____4143) ->
                                  let uu____4148 =
                                    let uu____4149 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____4149.FStar_Syntax_Syntax.n  in
                                  (match uu____4148 with
                                   | FStar_Syntax_Syntax.Tm_type uu____4152
                                       -> false
                                   | uu____4153 -> true)) bs1
                          in
                       match uu____4093 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____4072 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____4391 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "tv_" uu____4391) type_vars
                             in
                          let tvar_context =
                            FStar_List.map2
                              (fun b  ->
                                 fun nm  ->
                                   ((FStar_Pervasives_Native.fst b), nm))
                              type_vars tvar_names
                             in
                          let rec aux loc accum_embeddings bs3 =
                            match bs3 with
                            | [] ->
                                let arg_unembeddings =
                                  FStar_List.rev accum_embeddings  in
                                let res_embedding =
                                  mk_embedding loc tvar_context result_typ
                                   in
                                let fv_lid2 =
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                let uu____4480 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____4480
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____4496 =
                                      let uu____4499 =
                                        let uu____4502 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____4503 =
                                          let uu____4506 =
                                            let uu____4507 =
                                              let uu____4508 =
                                                let uu____4509 =
                                                  let uu____4520 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____4520,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____4509
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____4508
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____4507
                                             in
                                          [uu____4506; fv_lid_embedded; cb]
                                           in
                                        uu____4502 :: uu____4503  in
                                      res_embedding :: uu____4499  in
                                    FStar_List.append arg_unembeddings
                                      uu____4496
                                     in
                                  let fun_embedding =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (embed_fun_N, args))
                                     in
                                  let tabs =
                                    abstract_tvars tvar_names fun_embedding
                                     in
                                  let cb_tabs = mk_lam "cb" tabs  in
                                  let uu____4542 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____4542, arity, true)
                                else
                                  (let uu____4549 =
                                     let uu____4550 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____4550
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____4549
                                   then
                                     let h =
                                       let uu____4558 =
                                         let uu____4559 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.strcat
                                           (mk_tactic_interpretation loc)
                                           uu____4559
                                          in
                                       str_to_top_name uu____4558  in
                                     let tac_fun =
                                       let uu____4567 =
                                         let uu____4568 =
                                           let uu____4575 =
                                             let uu____4576 =
                                               let uu____4577 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.strcat
                                                 (mk_from_tactic loc)
                                                 uu____4577
                                                in
                                             str_to_top_name uu____4576  in
                                           let uu____4584 =
                                             let uu____4587 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____4587]  in
                                           (uu____4575, uu____4584)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____4568
                                          in
                                       FStar_All.pipe_left w uu____4567  in
                                     let psc = str_to_name "psc"  in
                                     let ncb = str_to_name "ncb"  in
                                     let all_args = str_to_name "args"  in
                                     let args =
                                       FStar_List.append [tac_fun]
                                         (FStar_List.append arg_unembeddings
                                            [res_embedding; psc; ncb])
                                        in
                                     let tabs =
                                       match tvar_names with
                                       | [] ->
                                           let uu____4597 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____4597
                                       | uu____4600 ->
                                           let uu____4603 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____4603
                                        in
                                     let uu____4606 =
                                       let uu____4607 = mk_lam "ncb" tabs  in
                                       mk_lam "psc" uu____4607  in
                                     (uu____4606,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____4615 =
                                        let uu____4616 =
                                          let uu____4617 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.strcat
                                            "Plugins not defined for type "
                                            uu____4617
                                           in
                                        NoTacticEmbedding uu____4616  in
                                      FStar_Exn.raise uu____4615))
                            | (b,uu____4625)::bs4 ->
                                let uu____4645 =
                                  let uu____4648 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____4648 :: accum_embeddings  in
                                aux loc uu____4645 bs4
                             in
                          (try
                             (fun uu___276_4668  ->
                                match () with
                                | () ->
                                    let uu____4679 = aux Syntax_term [] bs2
                                       in
                                    (match uu____4679 with
                                     | (w1,a,b) ->
                                         let uu____4699 = aux NBE_t [] bs2
                                            in
                                         (match uu____4699 with
                                          | (w',uu____4717,uu____4718) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____4743 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____4743 msg);
                                FStar_Pervasives_Native.None))))
  