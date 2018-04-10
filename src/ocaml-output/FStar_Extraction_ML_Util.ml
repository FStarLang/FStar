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
      let uu____119 =
        let uu____120 =
          let uu____121 =
            let uu____132 = FStar_Util.string_of_int i  in
            (uu____132, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____121  in
        FStar_All.pipe_right uu____120
          (fun _0_18  -> FStar_Extraction_ML_Syntax.MLE_Const _0_18)
         in
      FStar_All.pipe_right uu____119
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____148 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_19  -> FStar_Extraction_ML_Syntax.MLE_Const _0_19)
         in
      FStar_All.pipe_right uu____148
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____149 =
      let uu____156 =
        let uu____159 =
          let uu____160 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____160 cstr  in
        let uu____161 =
          let uu____164 =
            let uu____165 =
              let uu____166 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____166 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____165 cint  in
          let uu____167 =
            let uu____170 =
              let uu____171 =
                let uu____172 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____172 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____171 cint  in
            let uu____173 =
              let uu____176 =
                let uu____177 =
                  let uu____178 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____178 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____177 cint  in
              let uu____179 =
                let uu____182 =
                  let uu____183 =
                    let uu____184 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____184 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____183 cint  in
                [uu____182]  in
              uu____176 :: uu____179  in
            uu____170 :: uu____173  in
          uu____164 :: uu____167  in
        uu____159 :: uu____161  in
      (mk_range_mle, uu____156)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____149
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____198 ->
          let uu____199 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____199
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____223 =
            FStar_Util.find_opt
              (fun uu____237  ->
                 match uu____237 with | (y,uu____243) -> y = x) subst1
             in
          (match uu____223 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____260 =
            let uu____267 = subst_aux subst1 t1  in
            let uu____268 = subst_aux subst1 t2  in (uu____267, f, uu____268)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____260
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____275 =
            let uu____282 = FStar_List.map (subst_aux subst1) args  in
            (uu____282, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____275
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____290 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____290
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____305  ->
    fun args  ->
      match uu____305 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____316 =
               let uu____317 = FStar_List.zip formals args  in
               subst_aux uu____317 t  in
             FStar_Pervasives_Native.Some uu____316)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____346 = try_subst ts args  in
      match uu____346 with
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
    fun uu___61_361  ->
      match uu___61_361 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____370 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____370 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____376 = try_subst ts args  in
               (match uu____376 with
                | FStar_Pervasives_Native.None  ->
                    let uu____381 =
                      let uu____382 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____383 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____384 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____382 uu____383 uu____384
                       in
                    failwith uu____381
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____388 -> FStar_Pervasives_Native.None)
      | uu____391 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____402) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____403 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___62_412  ->
    match uu___62_412 with
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
        | uu____428 ->
            let uu____433 =
              let uu____434 = FStar_Range.string_of_range r  in
              let uu____435 = eff_to_string f  in
              let uu____436 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____434
                uu____435 uu____436
               in
            failwith uu____433
  
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
    (fun uu____473  ->
       fun t  ->
         match uu____473 with
         | (uu____479,t0) ->
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
                | uu____585 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____617 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____624 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____624 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____634;
                     FStar_Extraction_ML_Syntax.loc = uu____635;_}
                   ->
                   let uu____656 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____656
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____672 = type_leq unfold_ty t2 t2'  in
                        (if uu____672
                         then
                           let body1 =
                             let uu____683 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____683
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____688 =
                             let uu____691 =
                               let uu____692 =
                                 let uu____696 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____696
                                  in
                               FStar_All.pipe_left uu____692
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____691  in
                           (true, uu____688)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____725 =
                           let uu____732 =
                             let uu____735 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_20  ->
                                  FStar_Pervasives_Native.Some _0_20)
                               uu____735
                              in
                           type_leq_c unfold_ty uu____732 t2 t2'  in
                         match uu____725 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____759 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____759
                               | uu____768 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____776 ->
                   let uu____779 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____779
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____815 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____815
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____831 = unfold_ty t  in
                 match uu____831 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____845 = unfold_ty t'  in
                     (match uu____845 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____867 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____867
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____884,uu____885) ->
              let uu____892 = unfold_ty t  in
              (match uu____892 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____906 -> (false, FStar_Pervasives_Native.None))
          | (uu____911,FStar_Extraction_ML_Syntax.MLTY_Named uu____912) ->
              let uu____919 = unfold_ty t'  in
              (match uu____919 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____933 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____940 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____952 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____952 FStar_Pervasives_Native.fst

let is_type_abstraction :
  'a 'b 'c .
    (('a,'b) FStar_Util.either,'c) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.bool
  =
  fun uu___63_995  ->
    match uu___63_995 with
    | (FStar_Util.Inl uu____1006,uu____1007)::uu____1008 -> true
    | uu____1031 -> false
  
let (is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1054  ->
    match uu____1054 with
    | (ns,n1) ->
        let uu____1069 =
          let uu____1070 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____1070  in
        if uu____1069
        then
          let uu____1073 =
            let uu____1074 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____1074  in
          FStar_Pervasives_Native.Some uu____1073
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1087 = is_xtuple mlp  in
        (match uu____1087 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1091 -> e)
    | uu____1094 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___64_1103  ->
    match uu___64_1103 with
    | f::uu____1109 ->
        let uu____1112 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1112 with
         | (ns,uu____1122) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1133 -> failwith "impos"
  
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
  fun uu____1189  ->
    match uu____1189 with
    | (ns,n1) ->
        let uu____1204 =
          let uu____1205 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1205  in
        if uu____1204
        then
          let uu____1208 =
            let uu____1209 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1209  in
          FStar_Pervasives_Native.Some uu____1208
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1222 = is_xtuple_ty mlp  in
        (match uu____1222 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1226 -> t)
    | uu____1229 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1239 = codegen_fsharp ()  in
    if uu____1239
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1251  ->
    match uu____1251 with
    | (ns,n1) ->
        let uu____1264 = codegen_fsharp ()  in
        if uu____1264
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____1277 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1277, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1303 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1303
      then true
      else
        (let uu____1305 = unfold_ty t  in
         match uu____1305 with
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
            let uu____1331 =
              let uu____1338 = eraseTypeDeep unfold_ty tyd  in
              let uu____1342 = eraseTypeDeep unfold_ty tycd  in
              (uu____1338, etag, uu____1342)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1331
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1353 = erasableType unfold_ty t  in
          if uu____1353
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1358 =
               let uu____1365 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1365, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1358)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1376 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1376
      | uu____1382 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1385 =
    let uu____1389 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1389  in
  FStar_All.pipe_left uu____1385
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
          let uu____1462 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1462
  
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1474 = FStar_Range.file_of_range r  in (line, uu____1474)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1493,b) ->
        let uu____1495 = doms_and_cod b  in
        (match uu____1495 with | (ds,c) -> ((a :: ds), c))
    | uu____1516 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1528 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1528
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1555,b) ->
        let uu____1557 = uncurry_mlty_fun b  in
        (match uu____1557 with | (args,res) -> ((a :: args), res))
    | uu____1578 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____1589 -> true
    | uu____1590 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____1597 -> uu____1597
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1613 =
          let uu____1618 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1618)  in
        FStar_Errors.log_issue r uu____1613
  
type emb_loc =
  | S 
  | R [@@deriving show]
let (uu___is_S : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | S  -> true | uu____1624 -> false 
let (uu___is_R : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | R  -> true | uu____1630 -> false 
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
            let uu____1669 =
              let uu____1670 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1670  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1669
             in
          let lid_to_top_name l =
            let uu____1676 =
              let uu____1677 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1677  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1676
             in
          let str_to_name s =
            let uu____1683 = FStar_Ident.lid_of_str s  in
            lid_to_name uu____1683  in
          let str_to_top_name s =
            let uu____1689 = FStar_Ident.lid_of_str s  in
            lid_to_top_name uu____1689  in
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
            let uu____1721 =
              let uu____1722 = FStar_Util.string_of_int arity  in
              Prims.strcat "embed_arrow_" uu____1722  in
            fstar_syn_emb_prefix uu____1721  in
          let mk_any_embedding s =
            let uu____1728 =
              let uu____1729 =
                let uu____1736 = fstar_syn_emb_prefix "mk_any_emb"  in
                let uu____1737 =
                  let uu____1740 = str_to_name s  in [uu____1740]  in
                (uu____1736, uu____1737)  in
              FStar_Extraction_ML_Syntax.MLE_App uu____1729  in
            FStar_All.pipe_left w uu____1728  in
          let mk_lam nm e =
            FStar_All.pipe_left w
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
             in
          let known_type_constructors =
            let uu____1777 =
              let uu____1788 =
                let uu____1799 =
                  let uu____1810 =
                    let uu____1821 =
                      let uu____1830 =
                        FStar_Reflection_Data.fstar_refl_types_lid "term"  in
                      (uu____1830, (Prims.parse_int "0"), "term", R)  in
                    let uu____1831 =
                      let uu____1842 =
                        let uu____1851 =
                          FStar_Reflection_Data.fstar_refl_types_lid "fv"  in
                        (uu____1851, (Prims.parse_int "0"), "fv", R)  in
                      let uu____1852 =
                        let uu____1863 =
                          let uu____1872 =
                            FStar_Reflection_Data.fstar_refl_types_lid
                              "binder"
                             in
                          (uu____1872, (Prims.parse_int "0"), "binder", R)
                           in
                        let uu____1873 =
                          let uu____1884 =
                            let uu____1893 =
                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                "binders"
                               in
                            (uu____1893, (Prims.parse_int "0"), "binders", R)
                             in
                          let uu____1894 =
                            let uu____1905 =
                              let uu____1916 =
                                let uu____1927 =
                                  let uu____1938 =
                                    let uu____1947 =
                                      FStar_Parser_Const.mk_tuple_lid
                                        (Prims.parse_int "2")
                                        FStar_Range.dummyRange
                                       in
                                    (uu____1947, (Prims.parse_int "2"),
                                      "tuple2", S)
                                     in
                                  let uu____1948 =
                                    let uu____1959 =
                                      let uu____1968 =
                                        FStar_Reflection_Data.fstar_refl_data_lid
                                          "exp"
                                         in
                                      (uu____1968, (Prims.parse_int "0"),
                                        "exp", R)
                                       in
                                    [uu____1959]  in
                                  uu____1938 :: uu____1948  in
                                (FStar_Parser_Const.option_lid,
                                  (Prims.parse_int "1"), "option", S) ::
                                  uu____1927
                                 in
                              (FStar_Parser_Const.list_lid,
                                (Prims.parse_int "1"), "list", S) ::
                                uu____1916
                               in
                            (FStar_Parser_Const.norm_step_lid,
                              (Prims.parse_int "0"), "norm_step", S) ::
                              uu____1905
                             in
                          uu____1884 :: uu____1894  in
                        uu____1863 :: uu____1873  in
                      uu____1842 :: uu____1852  in
                    uu____1821 :: uu____1831  in
                  (FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                    "string", S) :: uu____1810
                   in
                (FStar_Parser_Const.unit_lid, (Prims.parse_int "0"), "unit",
                  S) :: uu____1799
                 in
              (FStar_Parser_Const.bool_lid, (Prims.parse_int "0"), "bool", S)
                :: uu____1788
               in
            (FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int", S) ::
              uu____1777
             in
          let is_known_type_constructor fv1 n1 =
            FStar_Util.for_some
              (fun uu____2103  ->
                 match uu____2103 with
                 | (x,args,uu____2114,uu____2115) ->
                     (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
              known_type_constructors
             in
          let find_env_entry bv uu____2128 =
            match uu____2128 with
            | (bv',uu____2134) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
          let rec mk_embedding env t2 =
            let uu____2156 =
              let uu____2157 = FStar_Syntax_Subst.compress t2  in
              uu____2157.FStar_Syntax_Syntax.n  in
            match uu____2156 with
            | FStar_Syntax_Syntax.Tm_name bv when
                FStar_Util.for_some (find_env_entry bv) env ->
                let uu____2165 =
                  let uu____2166 =
                    let uu____2171 =
                      FStar_Util.find_opt (find_env_entry bv) env  in
                    FStar_Util.must uu____2171  in
                  FStar_Pervasives_Native.snd uu____2166  in
                FStar_All.pipe_left mk_any_embedding uu____2165
            | FStar_Syntax_Syntax.Tm_refine (x,uu____2187) ->
                mk_embedding env x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t3,uu____2193,uu____2194) ->
                mk_embedding env t3
            | uu____2235 ->
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
                let uu____2237 = FStar_Syntax_Util.head_and_args t3  in
                (match uu____2237 with
                 | (head1,args) ->
                     let n_args = FStar_List.length args  in
                     let uu____2281 =
                       let uu____2282 = FStar_Syntax_Util.un_uinst head1  in
                       uu____2282.FStar_Syntax_Syntax.n  in
                     (match uu____2281 with
                      | FStar_Syntax_Syntax.Tm_refine (b,uu____2286) ->
                          mk_embedding env b.FStar_Syntax_Syntax.sort
                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                          is_known_type_constructor fv1 n_args ->
                          let arg_embeddings =
                            FStar_List.map
                              (fun uu____2306  ->
                                 match uu____2306 with
                                 | (t4,uu____2312) -> mk_embedding env t4)
                              args
                             in
                          let nm =
                            (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                             in
                          let uu____2314 =
                            let uu____2323 =
                              FStar_Util.find_opt
                                (fun uu____2347  ->
                                   match uu____2347 with
                                   | (x,uu____2357,uu____2358,uu____2359) ->
                                       FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                known_type_constructors
                               in
                            FStar_All.pipe_right uu____2323 FStar_Util.must
                             in
                          (match uu____2314 with
                           | (uu____2386,t_arity,trepr_head,loc_embedding) ->
                               let head2 =
                                 mk_basic_embedding loc_embedding nm  in
                               (match t_arity with
                                | _0_21 when _0_21 = (Prims.parse_int "0") ->
                                    head2
                                | n1 ->
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (head2, arg_embeddings))))
                      | uu____2394 ->
                          let uu____2395 =
                            let uu____2396 =
                              let uu____2397 =
                                FStar_Syntax_Print.term_to_string t3  in
                              Prims.strcat "Embedding not defined for type "
                                uu____2397
                               in
                            NoTacticEmbedding uu____2396  in
                          FStar_Exn.raise uu____2395))
             in
          let abstract_tvars tvar_names body =
            match tvar_names with
            | [] -> body
            | uu____2411 ->
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
                  let uu____2451 =
                    let uu____2452 =
                      let uu____2453 =
                        let uu____2460 =
                          let uu____2463 = str_to_name "args_tail"  in
                          [uu____2463]  in
                        (body, uu____2460)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2453  in
                    FStar_All.pipe_left w uu____2452  in
                  (pattern, FStar_Pervasives_Native.None, uu____2451)  in
                let default_branch =
                  let uu____2477 =
                    let uu____2478 =
                      let uu____2479 =
                        let uu____2486 = str_to_name "failwith"  in
                        let uu____2487 =
                          let uu____2490 =
                            let uu____2491 =
                              mlexpr_of_const FStar_Range.dummyRange
                                (FStar_Const.Const_string
                                   ("arity mismatch", FStar_Range.dummyRange))
                               in
                            FStar_All.pipe_left w uu____2491  in
                          [uu____2490]  in
                        (uu____2486, uu____2487)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2479  in
                    FStar_All.pipe_left w uu____2478  in
                  (FStar_Extraction_ML_Syntax.MLP_Wild,
                    FStar_Pervasives_Native.None, uu____2477)
                   in
                let body1 =
                  let uu____2497 =
                    let uu____2498 =
                      let uu____2513 = str_to_name "args"  in
                      (uu____2513, [branch1; default_branch])  in
                    FStar_Extraction_ML_Syntax.MLE_Match uu____2498  in
                  FStar_All.pipe_left w uu____2497  in
                mk_lam "args" body1
             in
          let uu____2548 = FStar_Syntax_Util.arrow_formals_comp t1  in
          match uu____2548 with
          | (bs,c) ->
              let result_typ = FStar_Syntax_Util.comp_result c  in
              let arity = FStar_List.length bs  in
              let uu____2589 =
                let uu____2606 =
                  FStar_Util.prefix_until
                    (fun uu____2640  ->
                       match uu____2640 with
                       | (b,uu____2646) ->
                           let uu____2647 =
                             let uu____2648 =
                               FStar_Syntax_Subst.compress
                                 b.FStar_Syntax_Syntax.sort
                                in
                             uu____2648.FStar_Syntax_Syntax.n  in
                           (match uu____2647 with
                            | FStar_Syntax_Syntax.Tm_type uu____2651 -> false
                            | uu____2652 -> true)) bs
                   in
                match uu____2606 with
                | FStar_Pervasives_Native.None  -> (bs, [])
                | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                    (tvars, (x :: rest))
                 in
              (match uu____2589 with
               | (type_vars,bs1) ->
                   let non_tvar_arity = FStar_List.length bs1  in
                   let tvar_names =
                     FStar_List.mapi
                       (fun i  ->
                          fun tv  ->
                            let uu____2835 = FStar_Util.string_of_int i  in
                            Prims.strcat "tv_" uu____2835) type_vars
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
                         let uu____2924 = FStar_Syntax_Util.is_pure_comp c
                            in
                         if uu____2924
                         then
                           let embed_fun_N =
                             mk_arrow_embedding non_tvar_arity  in
                           let args =
                             let uu____2943 =
                               let uu____2946 =
                                 let uu____2949 = lid_to_top_name fv  in
                                 [uu____2949]  in
                               res_embedding :: uu____2946  in
                             FStar_List.append arg_unembeddings uu____2943
                              in
                           let fun_embedding =
                             FStar_All.pipe_left w
                               (FStar_Extraction_ML_Syntax.MLE_App
                                  (embed_fun_N, args))
                              in
                           let tabs = abstract_tvars tvar_names fun_embedding
                              in
                           let uu____2954 =
                             let uu____2961 = mk_lam "_psc" tabs  in
                             (uu____2961, arity, true)  in
                           FStar_Pervasives_Native.Some uu____2954
                         else
                           (let uu____2973 =
                              let uu____2974 =
                                FStar_TypeChecker_Env.norm_eff_name tcenv
                                  (FStar_Syntax_Util.comp_effect_name c)
                                 in
                              FStar_Ident.lid_equals uu____2974
                                FStar_Parser_Const.effect_TAC_lid
                               in
                            if uu____2973
                            then
                              let h =
                                let uu____2984 =
                                  let uu____2985 =
                                    FStar_Util.string_of_int non_tvar_arity
                                     in
                                  Prims.strcat
                                    "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                                    uu____2985
                                   in
                                str_to_top_name uu____2984  in
                              let tac_fun =
                                let uu____2993 =
                                  let uu____2994 =
                                    let uu____3001 =
                                      let uu____3002 =
                                        let uu____3003 =
                                          FStar_Util.string_of_int
                                            non_tvar_arity
                                           in
                                        Prims.strcat
                                          "FStar_Tactics_Native.from_tactic_"
                                          uu____3003
                                         in
                                      str_to_top_name uu____3002  in
                                    let uu____3010 =
                                      let uu____3013 = lid_to_top_name fv  in
                                      [uu____3013]  in
                                    (uu____3001, uu____3010)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____2994
                                   in
                                FStar_All.pipe_left w uu____2993  in
                              let tac_lid_app =
                                let uu____3017 =
                                  let uu____3018 =
                                    let uu____3025 =
                                      str_to_top_name
                                        "FStar_Ident.lid_of_str"
                                       in
                                    (uu____3025, [w ml_fv])  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3018
                                   in
                                FStar_All.pipe_left w uu____3017  in
                              let psc = str_to_name "psc"  in
                              let all_args = str_to_name "args"  in
                              let args =
                                let uu____3033 =
                                  let uu____3036 =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_Bool
                                            true))
                                     in
                                  [uu____3036; tac_fun]  in
                                FStar_List.append uu____3033
                                  (FStar_List.append arg_unembeddings
                                     [res_embedding; tac_lid_app; psc])
                                 in
                              let tabs =
                                match tvar_names with
                                | [] ->
                                    let uu____3038 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h,
                                             (FStar_List.append args
                                                [all_args])))
                                       in
                                    mk_lam "args" uu____3038
                                | uu____3041 ->
                                    let uu____3044 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h, args))
                                       in
                                    abstract_tvars tvar_names uu____3044
                                 in
                              let uu____3047 =
                                let uu____3054 = mk_lam "psc" tabs  in
                                (uu____3054, (arity + (Prims.parse_int "1")),
                                  false)
                                 in
                              FStar_Pervasives_Native.Some uu____3047
                            else
                              (let uu____3068 =
                                 let uu____3069 =
                                   let uu____3070 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   Prims.strcat
                                     "Plugins not defined for type "
                                     uu____3070
                                    in
                                 NoTacticEmbedding uu____3069  in
                               FStar_Exn.raise uu____3068))
                     | (b,uu____3080)::bs3 ->
                         let uu____3092 =
                           let uu____3095 =
                             mk_embedding env b.FStar_Syntax_Syntax.sort  in
                           uu____3095 :: accum_embeddings  in
                         aux uu____3092 env bs3
                      in
                   (try aux [] tvar_context bs1
                    with
                    | NoTacticEmbedding msg ->
                        let uu____3127 =
                          let uu____3128 = FStar_Ident.string_of_lid fv  in
                          not_implemented_warning t1.FStar_Syntax_Syntax.pos
                            uu____3128 msg
                           in
                        FStar_Pervasives_Native.None))
  