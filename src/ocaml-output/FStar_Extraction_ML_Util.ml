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
    | FStar_Const.Const_bytearray (bytes,uu____81) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____87) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____88 ->
        failwith "Unhandled constant: reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const' c
      with
      | uu____105 ->
          let uu____106 =
            let uu____107 = FStar_Range.string_of_range p  in
            let uu____108 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____107 uu____108
             in
          failwith uu____106
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____120 =
        let uu____121 =
          let uu____122 =
            let uu____133 = FStar_Util.string_of_int i  in
            (uu____133, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____122  in
        FStar_All.pipe_right uu____121
          (fun _0_18  -> FStar_Extraction_ML_Syntax.MLE_Const _0_18)
         in
      FStar_All.pipe_right uu____120
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____150 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_19  -> FStar_Extraction_ML_Syntax.MLE_Const _0_19)
         in
      FStar_All.pipe_right uu____150
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____151 =
      let uu____158 =
        let uu____161 =
          let uu____162 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____162 cstr  in
        let uu____163 =
          let uu____166 =
            let uu____167 =
              let uu____168 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____168 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____167 cint  in
          let uu____169 =
            let uu____172 =
              let uu____173 =
                let uu____174 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____174 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____173 cint  in
            let uu____175 =
              let uu____178 =
                let uu____179 =
                  let uu____180 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____180 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____179 cint  in
              let uu____181 =
                let uu____184 =
                  let uu____185 =
                    let uu____186 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____186 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____185 cint  in
                [uu____184]  in
              uu____178 :: uu____181  in
            uu____172 :: uu____175  in
          uu____166 :: uu____169  in
        uu____161 :: uu____163  in
      (mk_range_mle, uu____158)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____151
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____200 ->
          let uu____201 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____201
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____225 =
            FStar_Util.find_opt
              (fun uu____239  ->
                 match uu____239 with | (y,uu____245) -> y = x) subst1
             in
          (match uu____225 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____262 =
            let uu____269 = subst_aux subst1 t1  in
            let uu____270 = subst_aux subst1 t2  in (uu____269, f, uu____270)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____262
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____277 =
            let uu____284 = FStar_List.map (subst_aux subst1) args  in
            (uu____284, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____277
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____292 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____292
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____307  ->
    fun args  ->
      match uu____307 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____318 =
               let uu____319 = FStar_List.zip formals args  in
               subst_aux uu____319 t  in
             FStar_Pervasives_Native.Some uu____318)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____348 = try_subst ts args  in
      match uu____348 with
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
    fun uu___61_363  ->
      match uu___61_363 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____372 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____372 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____378 = try_subst ts args  in
               (match uu____378 with
                | FStar_Pervasives_Native.None  ->
                    let uu____383 =
                      let uu____384 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____385 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____386 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____384 uu____385 uu____386
                       in
                    failwith uu____383
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____390 -> FStar_Pervasives_Native.None)
      | uu____393 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____404) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____405 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___62_414  ->
    match uu___62_414 with
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
        | uu____430 ->
            let uu____435 =
              let uu____436 = FStar_Range.string_of_range r  in
              let uu____437 = eff_to_string f  in
              let uu____438 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____436
                uu____437 uu____438
               in
            failwith uu____435
  
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
    (fun uu____475  ->
       fun t  ->
         match uu____475 with
         | (uu____481,t0) ->
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
                               (fun _0_20  ->
                                  FStar_Pervasives_Native.Some _0_20)
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
  fun uu___63_1000  ->
    match uu___63_1000 with
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
        let uu____1092 = is_xtuple mlp  in
        (match uu____1092 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1096 -> e)
    | uu____1099 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___64_1108  ->
    match uu___64_1108 with
    | f::uu____1114 ->
        let uu____1117 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1117 with
         | (ns,uu____1127) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1138 -> failwith "impos"
  
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
  fun uu____1194  ->
    match uu____1194 with
    | (ns,n1) ->
        let uu____1209 =
          let uu____1210 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1210  in
        if uu____1209
        then
          let uu____1213 =
            let uu____1214 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1214  in
          FStar_Pervasives_Native.Some uu____1213
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1227 = is_xtuple_ty mlp  in
        (match uu____1227 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1231 -> t)
    | uu____1234 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1244 = codegen_fsharp ()  in
    if uu____1244
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1256  ->
    match uu____1256 with
    | (ns,n1) ->
        let uu____1269 = codegen_fsharp ()  in
        if uu____1269
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____1282 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1282, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1308 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1308
      then true
      else
        (let uu____1310 = unfold_ty t  in
         match uu____1310 with
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
            let uu____1336 =
              let uu____1343 = eraseTypeDeep unfold_ty tyd  in
              let uu____1347 = eraseTypeDeep unfold_ty tycd  in
              (uu____1343, etag, uu____1347)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1336
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1358 = erasableType unfold_ty t  in
          if uu____1358
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1363 =
               let uu____1370 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1370, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1363)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1381 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1381
      | uu____1387 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1390 =
    let uu____1395 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1395  in
  FStar_All.pipe_left uu____1390
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
          let uu____1468 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1468
  
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1480 = FStar_Range.file_of_range r  in (line, uu____1480)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1499,b) ->
        let uu____1501 = doms_and_cod b  in
        (match uu____1501 with | (ds,c) -> ((a :: ds), c))
    | uu____1522 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1534 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1534
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1561,b) ->
        let uu____1563 = uncurry_mlty_fun b  in
        (match uu____1563 with | (args,res) -> ((a :: args), res))
    | uu____1584 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____1595 -> true
    | uu____1596 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____1603 -> uu____1603
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1619 =
          let uu____1624 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1624)  in
        FStar_Errors.log_issue r uu____1619
  
type emb_loc =
  | S 
  | R [@@deriving show]
let (uu___is_S : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | S  -> true | uu____1630 -> false 
let (uu___is_R : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | R  -> true | uu____1636 -> false 
let (interpret_plugin_as_term_fun :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mlexpr' ->
          (FStar_Extraction_ML_Syntax.mlexpr,Prims.int,Prims.bool)
            FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun tcenv  ->
    fun fv  ->
      fun t  ->
        fun ml_fv  ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant] tcenv t
             in
          let w =
            FStar_Extraction_ML_Syntax.with_ty
              FStar_Extraction_ML_Syntax.MLTY_Top
             in
          let lid_to_name l =
            let uu____1677 =
              let uu____1678 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1678  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1677
             in
          let lid_to_top_name l =
            let uu____1685 =
              let uu____1686 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1686  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1685
             in
          let str_to_name s =
            let uu____1693 = FStar_Ident.lid_of_str s  in
            lid_to_name uu____1693  in
          let str_to_top_name s =
            let uu____1700 = FStar_Ident.lid_of_str s  in
            lid_to_top_name uu____1700  in
          let fstar_syn_emb_prefix s =
            str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)  in
          let fstar_refl_emb_prefix s =
            str_to_name (Prims.strcat "FStar_Reflection_Embeddings." s)  in
          let mk_basic_embedding l s =
            let emb_prefix =
              match l with
              | S  -> fstar_syn_emb_prefix
              | R  -> fstar_refl_emb_prefix  in
            emb_prefix (Prims.strcat "e_" s)  in
          let mk_arrow_embedding arity =
            let uu____1738 =
              let uu____1739 = FStar_Util.string_of_int arity  in
              Prims.strcat "embed_arrow_" uu____1739  in
            fstar_syn_emb_prefix uu____1738  in
          let mk_any_embedding s =
            let uu____1746 =
              let uu____1747 =
                let uu____1754 = fstar_syn_emb_prefix "mk_any_emb"  in
                let uu____1755 =
                  let uu____1758 = str_to_name s  in [uu____1758]  in
                (uu____1754, uu____1755)  in
              FStar_Extraction_ML_Syntax.MLE_App uu____1747  in
            FStar_All.pipe_left w uu____1746  in
          let mk_lam nm e =
            FStar_All.pipe_left w
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
             in
          let known_type_constructors =
            let uu____1797 =
              let uu____1808 =
                let uu____1819 =
                  let uu____1830 =
                    let uu____1841 =
                      let uu____1850 =
                        FStar_Reflection_Data.fstar_refl_types_lid "term"  in
                      (uu____1850, (Prims.parse_int "0"), "term", R)  in
                    let uu____1851 =
                      let uu____1862 =
                        let uu____1871 =
                          FStar_Reflection_Data.fstar_refl_types_lid "fv"  in
                        (uu____1871, (Prims.parse_int "0"), "fv", R)  in
                      let uu____1872 =
                        let uu____1883 =
                          let uu____1892 =
                            FStar_Reflection_Data.fstar_refl_types_lid
                              "binder"
                             in
                          (uu____1892, (Prims.parse_int "0"), "binder", R)
                           in
                        let uu____1893 =
                          let uu____1904 =
                            let uu____1913 =
                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                "binders"
                               in
                            (uu____1913, (Prims.parse_int "0"), "binders", R)
                             in
                          let uu____1914 =
                            let uu____1925 =
                              let uu____1936 =
                                let uu____1947 =
                                  let uu____1958 =
                                    let uu____1967 =
                                      FStar_Parser_Const.mk_tuple_lid
                                        (Prims.parse_int "2")
                                        FStar_Range.dummyRange
                                       in
                                    (uu____1967, (Prims.parse_int "2"),
                                      "tuple2", S)
                                     in
                                  let uu____1968 =
                                    let uu____1979 =
                                      let uu____1988 =
                                        FStar_Reflection_Data.fstar_refl_data_lid
                                          "exp"
                                         in
                                      (uu____1988, (Prims.parse_int "0"),
                                        "exp", R)
                                       in
                                    [uu____1979]  in
                                  uu____1958 :: uu____1968  in
                                (FStar_Parser_Const.option_lid,
                                  (Prims.parse_int "1"), "option", S) ::
                                  uu____1947
                                 in
                              (FStar_Parser_Const.list_lid,
                                (Prims.parse_int "1"), "list", S) ::
                                uu____1936
                               in
                            (FStar_Parser_Const.norm_step_lid,
                              (Prims.parse_int "0"), "norm_step", S) ::
                              uu____1925
                             in
                          uu____1904 :: uu____1914  in
                        uu____1883 :: uu____1893  in
                      uu____1862 :: uu____1872  in
                    uu____1841 :: uu____1851  in
                  (FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                    "string", S) :: uu____1830
                   in
                (FStar_Parser_Const.unit_lid, (Prims.parse_int "0"), "unit",
                  S) :: uu____1819
                 in
              (FStar_Parser_Const.bool_lid, (Prims.parse_int "0"), "bool", S)
                :: uu____1808
               in
            (FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int", S) ::
              uu____1797
             in
          let is_known_type_constructor fv1 n1 =
            FStar_Util.for_some
              (fun uu____2125  ->
                 match uu____2125 with
                 | (x,args,uu____2136,uu____2137) ->
                     (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
              known_type_constructors
             in
          let find_env_entry bv uu____2152 =
            match uu____2152 with
            | (bv',uu____2158) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
          let rec mk_embedding env t2 =
            let uu____2182 =
              let uu____2183 = FStar_Syntax_Subst.compress t2  in
              uu____2183.FStar_Syntax_Syntax.n  in
            match uu____2182 with
            | FStar_Syntax_Syntax.Tm_name bv when
                FStar_Util.for_some (find_env_entry bv) env ->
                let uu____2191 =
                  let uu____2192 =
                    let uu____2197 =
                      FStar_Util.find_opt (find_env_entry bv) env  in
                    FStar_Util.must uu____2197  in
                  FStar_Pervasives_Native.snd uu____2192  in
                FStar_All.pipe_left mk_any_embedding uu____2191
            | FStar_Syntax_Syntax.Tm_refine (x,uu____2213) ->
                mk_embedding env x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t3,uu____2219,uu____2220) ->
                mk_embedding env t3
            | uu____2261 ->
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
                let uu____2263 = FStar_Syntax_Util.head_and_args t3  in
                (match uu____2263 with
                 | (head1,args) ->
                     let n_args = FStar_List.length args  in
                     let uu____2307 =
                       let uu____2308 = FStar_Syntax_Util.un_uinst head1  in
                       uu____2308.FStar_Syntax_Syntax.n  in
                     (match uu____2307 with
                      | FStar_Syntax_Syntax.Tm_refine (b,uu____2312) ->
                          mk_embedding env b.FStar_Syntax_Syntax.sort
                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                          is_known_type_constructor fv1 n_args ->
                          let arg_embeddings =
                            FStar_List.map
                              (fun uu____2332  ->
                                 match uu____2332 with
                                 | (t4,uu____2338) -> mk_embedding env t4)
                              args
                             in
                          let nm =
                            (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                             in
                          let uu____2340 =
                            let uu____2349 =
                              FStar_Util.find_opt
                                (fun uu____2373  ->
                                   match uu____2373 with
                                   | (x,uu____2383,uu____2384,uu____2385) ->
                                       FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                known_type_constructors
                               in
                            FStar_All.pipe_right uu____2349 FStar_Util.must
                             in
                          (match uu____2340 with
                           | (uu____2412,t_arity,trepr_head,loc_embedding) ->
                               let head2 =
                                 mk_basic_embedding loc_embedding nm  in
                               (match t_arity with
                                | _0_21 when _0_21 = (Prims.parse_int "0") ->
                                    head2
                                | n1 ->
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (head2, arg_embeddings))))
                      | uu____2420 ->
                          let uu____2421 =
                            let uu____2422 =
                              let uu____2423 =
                                FStar_Syntax_Print.term_to_string t3  in
                              Prims.strcat "Embedding not defined for type "
                                uu____2423
                               in
                            NoTacticEmbedding uu____2422  in
                          FStar_Exn.raise uu____2421))
             in
          let abstract_tvars tvar_names body =
            match tvar_names with
            | [] -> body
            | uu____2439 ->
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
                  let uu____2482 =
                    let uu____2483 =
                      let uu____2484 =
                        let uu____2491 =
                          let uu____2494 = str_to_name "args_tail"  in
                          [uu____2494]  in
                        (body, uu____2491)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2484  in
                    FStar_All.pipe_left w uu____2483  in
                  (pattern, FStar_Pervasives_Native.None, uu____2482)  in
                let default_branch =
                  let uu____2508 =
                    let uu____2509 =
                      let uu____2510 =
                        let uu____2517 = str_to_name "failwith"  in
                        let uu____2518 =
                          let uu____2521 =
                            let uu____2522 =
                              mlexpr_of_const FStar_Range.dummyRange
                                (FStar_Const.Const_string
                                   ("arity mismatch", FStar_Range.dummyRange))
                               in
                            FStar_All.pipe_left w uu____2522  in
                          [uu____2521]  in
                        (uu____2517, uu____2518)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2510  in
                    FStar_All.pipe_left w uu____2509  in
                  (FStar_Extraction_ML_Syntax.MLP_Wild,
                    FStar_Pervasives_Native.None, uu____2508)
                   in
                let body1 =
                  let uu____2528 =
                    let uu____2529 =
                      let uu____2544 = str_to_name "args"  in
                      (uu____2544, [branch1; default_branch])  in
                    FStar_Extraction_ML_Syntax.MLE_Match uu____2529  in
                  FStar_All.pipe_left w uu____2528  in
                mk_lam "args" body1
             in
          let uu____2579 = FStar_Syntax_Util.arrow_formals_comp t1  in
          match uu____2579 with
          | (bs,c) ->
              let result_typ = FStar_Syntax_Util.comp_result c  in
              let arity = FStar_List.length bs  in
              let uu____2620 =
                let uu____2637 =
                  FStar_Util.prefix_until
                    (fun uu____2671  ->
                       match uu____2671 with
                       | (b,uu____2677) ->
                           let uu____2678 =
                             let uu____2679 =
                               FStar_Syntax_Subst.compress
                                 b.FStar_Syntax_Syntax.sort
                                in
                             uu____2679.FStar_Syntax_Syntax.n  in
                           (match uu____2678 with
                            | FStar_Syntax_Syntax.Tm_type uu____2682 -> false
                            | uu____2683 -> true)) bs
                   in
                match uu____2637 with
                | FStar_Pervasives_Native.None  -> (bs, [])
                | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                    (tvars, (x :: rest))
                 in
              (match uu____2620 with
               | (type_vars,bs1) ->
                   let non_tvar_arity = FStar_List.length bs1  in
                   let tvar_names =
                     FStar_List.mapi
                       (fun i  ->
                          fun tv  ->
                            let uu____2866 = FStar_Util.string_of_int i  in
                            Prims.strcat "tv_" uu____2866) type_vars
                      in
                   let tvar_context =
                     FStar_List.map2
                       (fun b  ->
                          fun nm  -> ((FStar_Pervasives_Native.fst b), nm))
                       type_vars tvar_names
                      in
                   let rec aux accum_embeddings env bs2 =
                     match bs2 with
                     | [] ->
                         let arg_unembeddings =
                           FStar_List.rev accum_embeddings  in
                         let res_embedding = mk_embedding env result_typ  in
                         let uu____2958 = FStar_Syntax_Util.is_pure_comp c
                            in
                         if uu____2958
                         then
                           let embed_fun_N =
                             mk_arrow_embedding non_tvar_arity  in
                           let args =
                             let uu____2977 =
                               let uu____2980 =
                                 let uu____2983 = lid_to_top_name fv  in
                                 [uu____2983]  in
                               res_embedding :: uu____2980  in
                             FStar_List.append arg_unembeddings uu____2977
                              in
                           let fun_embedding =
                             FStar_All.pipe_left w
                               (FStar_Extraction_ML_Syntax.MLE_App
                                  (embed_fun_N, args))
                              in
                           let tabs = abstract_tvars tvar_names fun_embedding
                              in
                           let uu____2988 =
                             let uu____2995 = mk_lam "_psc" tabs  in
                             (uu____2995, arity, true)  in
                           FStar_Pervasives_Native.Some uu____2988
                         else
                           (let uu____3007 =
                              let uu____3008 =
                                FStar_TypeChecker_Env.norm_eff_name tcenv
                                  (FStar_Syntax_Util.comp_effect_name c)
                                 in
                              FStar_Ident.lid_equals uu____3008
                                FStar_Parser_Const.effect_TAC_lid
                               in
                            if uu____3007
                            then
                              let h =
                                let uu____3018 =
                                  let uu____3019 =
                                    FStar_Util.string_of_int non_tvar_arity
                                     in
                                  Prims.strcat
                                    "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                                    uu____3019
                                   in
                                str_to_top_name uu____3018  in
                              let tac_fun =
                                let uu____3027 =
                                  let uu____3028 =
                                    let uu____3035 =
                                      let uu____3036 =
                                        let uu____3037 =
                                          FStar_Util.string_of_int
                                            non_tvar_arity
                                           in
                                        Prims.strcat
                                          "FStar_Tactics_Native.from_tactic_"
                                          uu____3037
                                         in
                                      str_to_top_name uu____3036  in
                                    let uu____3044 =
                                      let uu____3047 = lid_to_top_name fv  in
                                      [uu____3047]  in
                                    (uu____3035, uu____3044)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3028
                                   in
                                FStar_All.pipe_left w uu____3027  in
                              let tac_lid_app =
                                let uu____3051 =
                                  let uu____3052 =
                                    let uu____3059 =
                                      str_to_top_name
                                        "FStar_Ident.lid_of_str"
                                       in
                                    (uu____3059, [w ml_fv])  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3052
                                   in
                                FStar_All.pipe_left w uu____3051  in
                              let psc = str_to_name "psc"  in
                              let all_args = str_to_name "args"  in
                              let args =
                                let uu____3067 =
                                  let uu____3070 =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_Bool
                                            true))
                                     in
                                  [uu____3070; tac_fun]  in
                                FStar_List.append uu____3067
                                  (FStar_List.append arg_unembeddings
                                     [res_embedding; tac_lid_app; psc])
                                 in
                              let tabs =
                                match tvar_names with
                                | [] ->
                                    let uu____3072 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h,
                                             (FStar_List.append args
                                                [all_args])))
                                       in
                                    mk_lam "args" uu____3072
                                | uu____3075 ->
                                    let uu____3078 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h, args))
                                       in
                                    abstract_tvars tvar_names uu____3078
                                 in
                              let uu____3081 =
                                let uu____3088 = mk_lam "psc" tabs  in
                                (uu____3088, (arity + (Prims.parse_int "1")),
                                  false)
                                 in
                              FStar_Pervasives_Native.Some uu____3081
                            else
                              (let uu____3102 =
                                 let uu____3103 =
                                   let uu____3104 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   Prims.strcat
                                     "Plugins not defined for type "
                                     uu____3104
                                    in
                                 NoTacticEmbedding uu____3103  in
                               FStar_Exn.raise uu____3102))
                     | (b,uu____3114)::bs3 ->
                         let uu____3126 =
                           let uu____3129 =
                             mk_embedding env b.FStar_Syntax_Syntax.sort  in
                           uu____3129 :: accum_embeddings  in
                         aux uu____3126 env bs3
                      in
                   (try aux [] tvar_context bs1
                    with
                    | NoTacticEmbedding msg ->
                        ((let uu____3162 = FStar_Ident.string_of_lid fv  in
                          not_implemented_warning t1.FStar_Syntax_Syntax.pos
                            uu____3162 msg);
                         FStar_Pervasives_Native.None)))
  