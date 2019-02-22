open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____6  ->
    let uu____7 = FStar_Options.codegen ()  in
    uu____7 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____76 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____106) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____112) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____117 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____121 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try (fun uu___47_135  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___46_138 ->
          let uu____139 =
            let uu____141 = FStar_Range.string_of_range p  in
            let uu____143 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____141 uu____143
             in
          failwith uu____139
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____160 =
        let uu____161 =
          let uu____162 =
            let uu____174 = FStar_Util.string_of_int i  in
            (uu____174, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____162  in
        FStar_All.pipe_right uu____161
          (fun _0_1  -> FStar_Extraction_ML_Syntax.MLE_Const _0_1)
         in
      FStar_All.pipe_right uu____160
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____195 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_2  -> FStar_Extraction_ML_Syntax.MLE_Const _0_2)
         in
      FStar_All.pipe_right uu____195
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____196 =
      let uu____203 =
        let uu____206 =
          let uu____207 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____207 cstr  in
        let uu____210 =
          let uu____213 =
            let uu____214 =
              let uu____216 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____216 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____214 cint  in
          let uu____219 =
            let uu____222 =
              let uu____223 =
                let uu____225 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____225 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____223 cint  in
            let uu____228 =
              let uu____231 =
                let uu____232 =
                  let uu____234 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____234 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____232 cint  in
              let uu____237 =
                let uu____240 =
                  let uu____241 =
                    let uu____243 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____243 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____241 cint  in
                [uu____240]  in
              uu____231 :: uu____237  in
            uu____222 :: uu____228  in
          uu____213 :: uu____219  in
        uu____206 :: uu____210  in
      (mk_range_mle, uu____203)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____196
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____260 ->
          let uu____261 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____261
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____289 =
            FStar_Util.find_opt
              (fun uu____305  ->
                 match uu____305 with | (y,uu____313) -> y = x) subst1
             in
          (match uu____289 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____337 =
            let uu____344 = subst_aux subst1 t1  in
            let uu____345 = subst_aux subst1 t2  in (uu____344, f, uu____345)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____337
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____352 =
            let uu____359 = FStar_List.map (subst_aux subst1) args  in
            (uu____359, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____352
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____367 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____367
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____383  ->
    fun args  ->
      match uu____383 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____397 =
               let uu____398 = FStar_List.zip formals args  in
               subst_aux uu____398 t  in
             FStar_Pervasives_Native.Some uu____397)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____430 = try_subst ts args  in
      match uu____430 with
      | FStar_Pervasives_Native.None  ->
          failwith
            "Substitution must be fully applied (see GitHub issue #490)"
      | FStar_Pervasives_Native.Some t -> t
  
let (udelta_unfold :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun uu___39_447  ->
      match uu___39_447 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____456 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____456 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____462 = try_subst ts args  in
               (match uu____462 with
                | FStar_Pervasives_Native.None  ->
                    let uu____467 =
                      let uu____469 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____471 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____473 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____469 uu____471 uu____473
                       in
                    failwith uu____467
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____480 -> FStar_Pervasives_Native.None)
      | uu____483 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____497) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____501 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___40_513  ->
    match uu___40_513 with
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
        | uu____534 ->
            let uu____539 =
              let uu____541 = FStar_Range.string_of_range r  in
              let uu____543 = eff_to_string f  in
              let uu____545 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____541
                uu____543 uu____545
               in
            failwith uu____539
  
let (join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
  
let (mk_ty_fun :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  FStar_List.fold_right
    (fun uu____588  ->
       fun t  ->
         match uu____588 with
         | (uu____595,t0) ->
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
          (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr
            FStar_Pervasives_Native.option))
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
                | uu____723 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____760 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____768 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____768 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____779;
                     FStar_Extraction_ML_Syntax.loc = uu____780;_}
                   ->
                   let uu____805 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____805
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____826 = type_leq unfold_ty t2 t2'  in
                        (if uu____826
                         then
                           let body1 =
                             let uu____840 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____840
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____848 =
                             let uu____851 =
                               let uu____852 =
                                 let uu____857 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____857
                                  in
                               FStar_All.pipe_left uu____852
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____851  in
                           (true, uu____848)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____897 =
                           let uu____905 =
                             let uu____908 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_3  ->
                                  FStar_Pervasives_Native.Some _0_3)
                               uu____908
                              in
                           type_leq_c unfold_ty uu____905 t2 t2'  in
                         match uu____897 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____935 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____935
                               | uu____946 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____958 ->
                   let uu____961 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____961
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____1007 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____1007
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____1032 = unfold_ty t  in
                 match uu____1032 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____1047 = unfold_ty t'  in
                     (match uu____1047 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____1072 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____1072
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____1099,uu____1100) ->
              let uu____1107 = unfold_ty t  in
              (match uu____1107 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____1122 -> (false, FStar_Pervasives_Native.None))
          | (uu____1129,FStar_Extraction_ML_Syntax.MLTY_Named uu____1130) ->
              let uu____1137 = unfold_ty t'  in
              (match uu____1137 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____1152 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____1163 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____1178 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____1178 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1209 =
          let uu____1216 = erase_effect_annotations t1  in
          let uu____1217 = erase_effect_annotations t2  in
          (uu____1216, FStar_Extraction_ML_Syntax.E_PURE, uu____1217)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____1209
    | uu____1218 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___41_1246  ->
    match uu___41_1246 with
    | (FStar_Util.Inl uu____1258,uu____1259)::uu____1260 -> true
    | uu____1284 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1312  ->
    match uu____1312 with
    | (ns,n1) ->
        let uu____1334 =
          let uu____1336 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____1336  in
        if uu____1334
        then
          let uu____1346 =
            let uu____1348 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____1348  in
          FStar_Pervasives_Native.Some uu____1346
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1367 = is_xtuple mlp  in
        (match uu____1367 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1374 -> e)
    | uu____1378 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___42_1389  ->
    match uu___42_1389 with
    | f::uu____1396 ->
        let uu____1399 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1399 with
         | (ns,uu____1410) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1423 -> failwith "impos"
  
let record_fields :
  'a .
    FStar_Ident.lident Prims.list ->
      'a Prims.list -> (Prims.string * 'a) Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2
        (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e))
        fs vs
  
let (is_xtuple_ty :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1489  ->
    match uu____1489 with
    | (ns,n1) ->
        let uu____1511 =
          let uu____1513 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1513  in
        if uu____1511
        then
          let uu____1523 =
            let uu____1525 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1525  in
          FStar_Pervasives_Native.Some uu____1523
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1544 = is_xtuple_ty mlp  in
        (match uu____1544 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1551 -> t)
    | uu____1555 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1569 = codegen_fsharp ()  in
    if uu____1569
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____1591  ->
    match uu____1591 with
    | (ns,n1) ->
        let uu____1611 = codegen_fsharp ()  in
        if uu____1611
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____1639 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1639, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1673 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1673
      then true
      else
        (let uu____1680 = unfold_ty t  in
         match uu____1680 with
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
            let uu____1710 =
              let uu____1717 = eraseTypeDeep unfold_ty tyd  in
              let uu____1721 = eraseTypeDeep unfold_ty tycd  in
              (uu____1717, etag, uu____1721)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1710
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1733 = erasableType unfold_ty t  in
          if uu____1733
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1741 =
               let uu____1748 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1748, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1741)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1759 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1759
      | uu____1765 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1776 =
    let uu____1781 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1781  in
  FStar_All.pipe_left uu____1776
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
          let uu____1869 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1869
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1885 = FStar_Range.file_of_range r  in (line, uu____1885)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1908,b) ->
        let uu____1910 = doms_and_cod b  in
        (match uu____1910 with | (ds,c) -> ((a :: ds), c))
    | uu____1931 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1944 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1944
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1972,b) ->
        let uu____1974 = uncurry_mlty_fun b  in
        (match uu____1974 with | (args,res) -> ((a :: args), res))
    | uu____1995 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____2011 -> true
    | uu____2014 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____2025 -> uu____2025
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____2047 =
          let uu____2053 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____2053)  in
        FStar_Errors.log_issue r uu____2047
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____2066 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____2077 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____2088 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____2099 -> false
  
type wrapped_term =
  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlexpr *
    Prims.int * Prims.bool)
let (interpret_plugin_as_term_fun :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ ->
        Prims.int FStar_Pervasives_Native.option ->
          FStar_Extraction_ML_Syntax.mlexpr' ->
            (FStar_Extraction_ML_Syntax.mlexpr *
              FStar_Extraction_ML_Syntax.mlexpr * Prims.int * Prims.bool)
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
              let uu____2170 =
                let uu____2171 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____2171  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2170
               in
            let lid_to_top_name l =
              let uu____2178 =
                let uu____2179 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____2179  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2178
               in
            let str_to_name s =
              let uu____2188 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____2188  in
            let str_to_top_name s =
              let uu____2197 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____2197  in
            let fstar_tc_nbe_prefix s =
              str_to_name (Prims.op_Hat "FStar_TypeChecker_NBETerm." s)  in
            let fstar_syn_emb_prefix s =
              str_to_name (Prims.op_Hat "FStar_Syntax_Embeddings." s)  in
            let fstar_refl_emb_prefix s =
              str_to_name (Prims.op_Hat "FStar_Reflection_Embeddings." s)  in
            let fstar_refl_nbeemb_prefix s =
              str_to_name (Prims.op_Hat "FStar_Reflection_NBEEmbeddings." s)
               in
            let fv_lid_embedded =
              let uu____2235 =
                let uu____2236 =
                  let uu____2243 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____2245 =
                    let uu____2248 =
                      let uu____2249 =
                        let uu____2250 =
                          let uu____2251 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____2251
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____2250  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____2249
                       in
                    [uu____2248]  in
                  (uu____2243, uu____2245)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2236  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2235
               in
            let emb_prefix uu___43_2266 =
              match uu___43_2266 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____2280 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____2291 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____2320 =
                let uu____2322 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____2322  in
              emb_prefix l uu____2320  in
            let mk_any_embedding l s =
              let uu____2338 =
                let uu____2339 =
                  let uu____2346 = emb_prefix l "mk_any_emb"  in
                  let uu____2348 =
                    let uu____2351 = str_to_name s  in [uu____2351]  in
                  (uu____2346, uu____2348)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2339  in
              FStar_All.pipe_left w uu____2338  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____2401 =
                let uu____2402 =
                  let uu____2409 = emb_prefix l "e_arrow"  in
                  (uu____2409, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2402  in
              FStar_All.pipe_left w uu____2401  in
            let known_type_constructors =
              let term_cs =
                let uu____2447 =
                  let uu____2462 =
                    let uu____2477 =
                      let uu____2492 =
                        let uu____2507 =
                          let uu____2522 =
                            let uu____2537 =
                              let uu____2552 =
                                let uu____2565 =
                                  let uu____2574 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____2574, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____2565, Syntax_term)  in
                              let uu____2588 =
                                let uu____2603 =
                                  let uu____2616 =
                                    let uu____2625 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____2625, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____2616, Refl_emb)  in
                                let uu____2639 =
                                  let uu____2654 =
                                    let uu____2667 =
                                      let uu____2676 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____2676, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____2667, Refl_emb)  in
                                  let uu____2690 =
                                    let uu____2705 =
                                      let uu____2718 =
                                        let uu____2727 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____2727, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____2718, Refl_emb)  in
                                    let uu____2741 =
                                      let uu____2756 =
                                        let uu____2769 =
                                          let uu____2778 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____2778, (Prims.parse_int "0"),
                                            "binders")
                                           in
                                        (uu____2769, Refl_emb)  in
                                      let uu____2792 =
                                        let uu____2807 =
                                          let uu____2820 =
                                            let uu____2829 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____2829,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____2820, Refl_emb)  in
                                        [uu____2807]  in
                                      uu____2756 :: uu____2792  in
                                    uu____2705 :: uu____2741  in
                                  uu____2654 :: uu____2690  in
                                uu____2603 :: uu____2639  in
                              uu____2552 :: uu____2588  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____2537
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____2522
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____2507
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____2492
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____2477
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____2462
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____2447
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___44_3136  ->
                     match uu___44_3136 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____3211 -> failwith "Impossible") term_cs
                 in
              fun uu___45_3237  ->
                match uu___45_3237 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____3252 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____3289  ->
                   match uu____3289 with
                   | ((x,args,uu____3305),uu____3306) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____3336 =
              match uu____3336 with
              | (bv',uu____3344) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____3378 =
                let uu____3379 = FStar_Syntax_Subst.compress t3  in
                uu____3379.FStar_Syntax_Syntax.n  in
              match uu____3378 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____3388 =
                    let uu____3390 =
                      let uu____3396 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____3396  in
                    FStar_Pervasives_Native.snd uu____3390  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____3388
              | FStar_Syntax_Syntax.Tm_refine (x,uu____3417) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____3423,uu____3424) ->
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____3497 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____3497 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____3519 =
                           let uu____3520 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____3520  in
                         uu____3519.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____3538 = mk_embedding l env t0  in
                       let uu____3539 = mk_embedding l env t11  in
                       emb_arrow l uu____3538 uu____3539)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____3610 =
                      let uu____3617 =
                        let uu____3618 =
                          let uu____3633 = FStar_Syntax_Syntax.mk_Total tail1
                             in
                          ([b], uu____3633)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____3618  in
                      FStar_Syntax_Syntax.mk uu____3617  in
                    uu____3610 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____3661 ->
                  let uu____3662 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3662 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3714 =
                         let uu____3715 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____3715.FStar_Syntax_Syntax.n  in
                       (match uu____3714 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3745  ->
                                      match uu____3745 with
                                      | (t4,uu____3753) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3760 =
                              let uu____3773 =
                                FStar_Util.find_opt
                                  (fun uu____3805  ->
                                     match uu____3805 with
                                     | ((x,uu____3820,uu____3821),uu____3822)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3773 FStar_Util.must
                               in
                            (match uu____3760 with
                             | ((uu____3873,t_arity,_trepr_head),loc_embedding)
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
                        | uu____3894 ->
                            let uu____3895 =
                              let uu____3896 =
                                let uu____3898 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____3898
                                 in
                              NoTacticEmbedding uu____3896  in
                            FStar_Exn.raise uu____3895))
              | FStar_Syntax_Syntax.Tm_uinst uu____3901 ->
                  let uu____3908 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3908 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3960 =
                         let uu____3961 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____3961.FStar_Syntax_Syntax.n  in
                       (match uu____3960 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3991  ->
                                      match uu____3991 with
                                      | (t4,uu____3999) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____4006 =
                              let uu____4019 =
                                FStar_Util.find_opt
                                  (fun uu____4051  ->
                                     match uu____4051 with
                                     | ((x,uu____4066,uu____4067),uu____4068)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____4019 FStar_Util.must
                               in
                            (match uu____4006 with
                             | ((uu____4119,t_arity,_trepr_head),loc_embedding)
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
                        | uu____4140 ->
                            let uu____4141 =
                              let uu____4142 =
                                let uu____4144 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____4144
                                 in
                              NoTacticEmbedding uu____4142  in
                            FStar_Exn.raise uu____4141))
              | FStar_Syntax_Syntax.Tm_app uu____4147 ->
                  let uu____4164 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____4164 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____4216 =
                         let uu____4217 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____4217.FStar_Syntax_Syntax.n  in
                       (match uu____4216 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____4247  ->
                                      match uu____4247 with
                                      | (t4,uu____4255) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____4262 =
                              let uu____4275 =
                                FStar_Util.find_opt
                                  (fun uu____4307  ->
                                     match uu____4307 with
                                     | ((x,uu____4322,uu____4323),uu____4324)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____4275 FStar_Util.must
                               in
                            (match uu____4262 with
                             | ((uu____4375,t_arity,_trepr_head),loc_embedding)
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
                        | uu____4396 ->
                            let uu____4397 =
                              let uu____4398 =
                                let uu____4400 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____4400
                                 in
                              NoTacticEmbedding uu____4398  in
                            FStar_Exn.raise uu____4397))
              | uu____4403 ->
                  let uu____4404 =
                    let uu____4405 =
                      let uu____4407 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____4407
                       in
                    NoTacticEmbedding uu____4405  in
                  FStar_Exn.raise uu____4404
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____4429 =
                      let uu____4430 =
                        let uu____4437 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____4439 =
                          let uu____4442 =
                            let uu____4443 =
                              let uu____4444 =
                                let uu____4445 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____4445
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____4444
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____4443
                             in
                          let uu____4447 =
                            let uu____4450 =
                              let uu____4451 =
                                let uu____4452 =
                                  let uu____4453 =
                                    let uu____4460 =
                                      let uu____4463 = str_to_name "args"  in
                                      [uu____4463]  in
                                    (body, uu____4460)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____4453
                                   in
                                FStar_All.pipe_left w uu____4452  in
                              mk_lam "_" uu____4451  in
                            [uu____4450]  in
                          uu____4442 :: uu____4447  in
                        (uu____4437, uu____4439)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____4430  in
                    FStar_All.pipe_left w uu____4429  in
                  mk_lam "args" body1
              | uu____4471 ->
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
                    let uu____4520 =
                      let uu____4521 =
                        let uu____4522 =
                          let uu____4529 =
                            let uu____4532 = str_to_name "args"  in
                            [uu____4532]  in
                          (body, uu____4529)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____4522  in
                      FStar_All.pipe_left w uu____4521  in
                    (pattern, FStar_Pervasives_Native.None, uu____4520)  in
                  let default_branch =
                    let uu____4547 =
                      let uu____4548 =
                        let uu____4549 =
                          let uu____4556 = str_to_name "failwith"  in
                          let uu____4558 =
                            let uu____4561 =
                              let uu____4562 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____4562  in
                            [uu____4561]  in
                          (uu____4556, uu____4558)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____4549  in
                      FStar_All.pipe_left w uu____4548  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____4547)
                     in
                  let body1 =
                    let uu____4570 =
                      let uu____4571 =
                        let uu____4586 = str_to_name "args"  in
                        (uu____4586, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____4571  in
                    FStar_All.pipe_left w uu____4570  in
                  let body2 =
                    let uu____4623 =
                      let uu____4624 =
                        let uu____4631 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____4633 =
                          let uu____4636 =
                            let uu____4637 =
                              let uu____4638 =
                                let uu____4639 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____4639
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____4638
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____4637
                             in
                          let uu____4641 =
                            let uu____4644 = mk_lam "_" body1  in
                            [uu____4644]  in
                          uu____4636 :: uu____4641  in
                        (uu____4631, uu____4633)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____4624  in
                    FStar_All.pipe_left w uu____4623  in
                  mk_lam "args" body2
               in
            let uu____4649 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____4649 with
            | (bs,c) ->
                let uu____4682 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____4783 = FStar_Util.first_N n1 bs  in
                           match uu____4783 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____4861 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____4861
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____4878 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____4880 = FStar_Util.string_of_int n1  in
                             let uu____4882 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____4878 uu____4880 uu____4882
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____4682 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____4939 =
                       let uu____4960 =
                         FStar_Util.prefix_until
                           (fun uu____5002  ->
                              match uu____5002 with
                              | (b,uu____5011) ->
                                  let uu____5016 =
                                    let uu____5017 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____5017.FStar_Syntax_Syntax.n  in
                                  (match uu____5016 with
                                   | FStar_Syntax_Syntax.Tm_type uu____5021
                                       -> false
                                   | uu____5023 -> true)) bs1
                          in
                       match uu____4960 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____4939 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____5265 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____5265) type_vars
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
                                let uu____5365 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____5365
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____5386 =
                                      let uu____5389 =
                                        let uu____5392 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____5393 =
                                          let uu____5396 =
                                            let uu____5397 =
                                              let uu____5398 =
                                                let uu____5399 =
                                                  let uu____5411 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____5411,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____5399
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____5398
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____5397
                                             in
                                          [uu____5396; fv_lid_embedded; cb]
                                           in
                                        uu____5392 :: uu____5393  in
                                      res_embedding :: uu____5389  in
                                    FStar_List.append arg_unembeddings
                                      uu____5386
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
                                  let uu____5436 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____5436, arity, true)
                                else
                                  (let uu____5450 =
                                     let uu____5452 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____5452
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____5450
                                   then
                                     let h =
                                       let uu____5463 =
                                         let uu____5465 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____5465
                                          in
                                       str_to_top_name uu____5463  in
                                     let tac_fun =
                                       let uu____5474 =
                                         let uu____5475 =
                                           let uu____5482 =
                                             let uu____5483 =
                                               let uu____5485 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____5485
                                                in
                                             str_to_top_name uu____5483  in
                                           let uu____5493 =
                                             let uu____5496 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____5496]  in
                                           (uu____5482, uu____5493)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____5475
                                          in
                                       FStar_All.pipe_left w uu____5474  in
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
                                           let uu____5510 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____5510
                                       | uu____5514 ->
                                           let uu____5518 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____5518
                                        in
                                     let uu____5521 =
                                       let uu____5522 = mk_lam "ncb" tabs  in
                                       mk_lam "psc" uu____5522  in
                                     (uu____5521,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____5537 =
                                        let uu____5538 =
                                          let uu____5540 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____5540
                                           in
                                        NoTacticEmbedding uu____5538  in
                                      FStar_Exn.raise uu____5537))
                            | (b,uu____5552)::bs4 ->
                                let uu____5572 =
                                  let uu____5575 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____5575 :: accum_embeddings  in
                                aux loc uu____5572 bs4
                             in
                          (try
                             (fun uu___49_5597  ->
                                match () with
                                | () ->
                                    let uu____5610 = aux Syntax_term [] bs2
                                       in
                                    (match uu____5610 with
                                     | (w1,a,b) ->
                                         let uu____5638 = aux NBE_t [] bs2
                                            in
                                         (match uu____5638 with
                                          | (w',uu____5660,uu____5661) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____5697 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____5697 msg);
                                FStar_Pervasives_Native.None))))
  