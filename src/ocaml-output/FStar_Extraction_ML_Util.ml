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
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____118 ->
        failwith "Unhandled constant: reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try (fun uu___9_132  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___8_135 ->
          let uu____136 =
            let uu____138 = FStar_Range.string_of_range p  in
            let uu____140 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____138 uu____140
             in
          failwith uu____136
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____157 =
        let uu____158 =
          let uu____159 =
            let uu____171 = FStar_Util.string_of_int i  in
            (uu____171, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____159  in
        FStar_All.pipe_right uu____158
          (fun _0_1  -> FStar_Extraction_ML_Syntax.MLE_Const _0_1)
         in
      FStar_All.pipe_right uu____157
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____192 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_2  -> FStar_Extraction_ML_Syntax.MLE_Const _0_2)
         in
      FStar_All.pipe_right uu____192
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____193 =
      let uu____200 =
        let uu____203 =
          let uu____204 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____204 cstr  in
        let uu____207 =
          let uu____210 =
            let uu____211 =
              let uu____213 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____213 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____211 cint  in
          let uu____216 =
            let uu____219 =
              let uu____220 =
                let uu____222 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____222 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____220 cint  in
            let uu____225 =
              let uu____228 =
                let uu____229 =
                  let uu____231 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____231 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____229 cint  in
              let uu____234 =
                let uu____237 =
                  let uu____238 =
                    let uu____240 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____240 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____238 cint  in
                [uu____237]  in
              uu____228 :: uu____234  in
            uu____219 :: uu____225  in
          uu____210 :: uu____216  in
        uu____203 :: uu____207  in
      (mk_range_mle, uu____200)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____193
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____257 ->
          let uu____258 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____258
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____286 =
            FStar_Util.find_opt
              (fun uu____302  ->
                 match uu____302 with | (y,uu____310) -> y = x) subst1
             in
          (match uu____286 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____334 =
            let uu____341 = subst_aux subst1 t1  in
            let uu____342 = subst_aux subst1 t2  in (uu____341, f, uu____342)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____334
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____349 =
            let uu____356 = FStar_List.map (subst_aux subst1) args  in
            (uu____356, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____349
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____364 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____364
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____380  ->
    fun args  ->
      match uu____380 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____394 =
               let uu____395 = FStar_List.zip formals args  in
               subst_aux uu____395 t  in
             FStar_Pervasives_Native.Some uu____394)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____427 = try_subst ts args  in
      match uu____427 with
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
    fun uu___1_444  ->
      match uu___1_444 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____453 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____453 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____459 = try_subst ts args  in
               (match uu____459 with
                | FStar_Pervasives_Native.None  ->
                    let uu____464 =
                      let uu____466 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____468 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____470 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____466 uu____468 uu____470
                       in
                    failwith uu____464
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____477 -> FStar_Pervasives_Native.None)
      | uu____480 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____494) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____498 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___2_510  ->
    match uu___2_510 with
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
        | uu____531 ->
            let uu____536 =
              let uu____538 = FStar_Range.string_of_range r  in
              let uu____540 = eff_to_string f  in
              let uu____542 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____538
                uu____540 uu____542
               in
            failwith uu____536
  
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
    (fun uu____585  ->
       fun t  ->
         match uu____585 with
         | (uu____592,t0) ->
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
                | uu____720 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____757 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____765 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____765 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____776;
                     FStar_Extraction_ML_Syntax.loc = uu____777;_}
                   ->
                   let uu____802 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____802
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____823 = type_leq unfold_ty t2 t2'  in
                        (if uu____823
                         then
                           let body1 =
                             let uu____837 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____837
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____845 =
                             let uu____848 =
                               let uu____849 =
                                 let uu____854 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____854
                                  in
                               FStar_All.pipe_left uu____849
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____848  in
                           (true, uu____845)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____894 =
                           let uu____902 =
                             let uu____905 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_3  ->
                                  FStar_Pervasives_Native.Some _0_3)
                               uu____905
                              in
                           type_leq_c unfold_ty uu____902 t2 t2'  in
                         match uu____894 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____932 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____932
                               | uu____943 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____955 ->
                   let uu____958 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____958
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____1004 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____1004
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____1029 = unfold_ty t  in
                 match uu____1029 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____1044 = unfold_ty t'  in
                     (match uu____1044 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____1069 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____1069
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____1096,uu____1097) ->
              let uu____1104 = unfold_ty t  in
              (match uu____1104 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____1119 -> (false, FStar_Pervasives_Native.None))
          | (uu____1126,FStar_Extraction_ML_Syntax.MLTY_Named uu____1127) ->
              let uu____1134 = unfold_ty t'  in
              (match uu____1134 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____1149 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____1160 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____1175 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____1175 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1206 =
          let uu____1213 = erase_effect_annotations t1  in
          let uu____1214 = erase_effect_annotations t2  in
          (uu____1213, FStar_Extraction_ML_Syntax.E_PURE, uu____1214)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____1206
    | uu____1215 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___3_1243  ->
    match uu___3_1243 with
    | (FStar_Util.Inl uu____1255,uu____1256)::uu____1257 -> true
    | uu____1281 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1309  ->
    match uu____1309 with
    | (ns,n1) ->
        let uu____1331 =
          let uu____1333 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____1333  in
        if uu____1331
        then
          let uu____1343 =
            let uu____1345 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____1345  in
          FStar_Pervasives_Native.Some uu____1343
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1364 = is_xtuple mlp  in
        (match uu____1364 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1371 -> e)
    | uu____1375 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___4_1386  ->
    match uu___4_1386 with
    | f::uu____1393 ->
        let uu____1396 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1396 with
         | (ns,uu____1407) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1420 -> failwith "impos"
  
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
  fun uu____1486  ->
    match uu____1486 with
    | (ns,n1) ->
        let uu____1508 =
          let uu____1510 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1510  in
        if uu____1508
        then
          let uu____1520 =
            let uu____1522 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1522  in
          FStar_Pervasives_Native.Some uu____1520
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1541 = is_xtuple_ty mlp  in
        (match uu____1541 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1548 -> t)
    | uu____1552 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1566 = codegen_fsharp ()  in
    if uu____1566
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____1588  ->
    match uu____1588 with
    | (ns,n1) ->
        let uu____1608 = codegen_fsharp ()  in
        if uu____1608
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____1636 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1636, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1670 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1670
      then true
      else
        (let uu____1677 = unfold_ty t  in
         match uu____1677 with
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
            let uu____1707 =
              let uu____1714 = eraseTypeDeep unfold_ty tyd  in
              let uu____1718 = eraseTypeDeep unfold_ty tycd  in
              (uu____1714, etag, uu____1718)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1707
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1730 = erasableType unfold_ty t  in
          if uu____1730
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1738 =
               let uu____1745 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1745, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1738)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1756 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1756
      | uu____1762 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1773 =
    let uu____1778 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1778  in
  FStar_All.pipe_left uu____1773
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
          let uu____1866 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1866
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1882 = FStar_Range.file_of_range r  in (line, uu____1882)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1905,b) ->
        let uu____1907 = doms_and_cod b  in
        (match uu____1907 with | (ds,c) -> ((a :: ds), c))
    | uu____1928 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1941 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1941
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1969,b) ->
        let uu____1971 = uncurry_mlty_fun b  in
        (match uu____1971 with | (args,res) -> ((a :: args), res))
    | uu____1992 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____2008 -> true
    | uu____2011 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____2022 -> uu____2022
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____2044 =
          let uu____2050 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____2050)  in
        FStar_Errors.log_issue r uu____2044
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____2063 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____2074 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____2085 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____2096 -> false
  
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
              let uu____2167 =
                let uu____2168 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____2168  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2167
               in
            let lid_to_top_name l =
              let uu____2175 =
                let uu____2176 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____2176  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2175
               in
            let str_to_name s =
              let uu____2185 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____2185  in
            let str_to_top_name s =
              let uu____2194 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____2194  in
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
              let uu____2232 =
                let uu____2233 =
                  let uu____2240 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____2242 =
                    let uu____2245 =
                      let uu____2246 =
                        let uu____2247 =
                          let uu____2248 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____2248
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____2247  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____2246
                       in
                    [uu____2245]  in
                  (uu____2240, uu____2242)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2233  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2232
               in
            let emb_prefix uu___5_2263 =
              match uu___5_2263 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____2277 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____2288 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____2317 =
                let uu____2319 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____2319  in
              emb_prefix l uu____2317  in
            let mk_any_embedding l s =
              let uu____2335 =
                let uu____2336 =
                  let uu____2343 = emb_prefix l "mk_any_emb"  in
                  let uu____2345 =
                    let uu____2348 = str_to_name s  in [uu____2348]  in
                  (uu____2343, uu____2345)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2336  in
              FStar_All.pipe_left w uu____2335  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____2398 =
                let uu____2399 =
                  let uu____2406 = emb_prefix l "e_arrow"  in
                  (uu____2406, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2399  in
              FStar_All.pipe_left w uu____2398  in
            let known_type_constructors =
              let term_cs =
                let uu____2444 =
                  let uu____2459 =
                    let uu____2474 =
                      let uu____2489 =
                        let uu____2504 =
                          let uu____2519 =
                            let uu____2534 =
                              let uu____2549 =
                                let uu____2562 =
                                  let uu____2571 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____2571, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____2562, Syntax_term)  in
                              let uu____2585 =
                                let uu____2600 =
                                  let uu____2613 =
                                    let uu____2622 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____2622, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____2613, Refl_emb)  in
                                let uu____2636 =
                                  let uu____2651 =
                                    let uu____2664 =
                                      let uu____2673 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____2673, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____2664, Refl_emb)  in
                                  let uu____2687 =
                                    let uu____2702 =
                                      let uu____2715 =
                                        let uu____2724 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____2724, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____2715, Refl_emb)  in
                                    let uu____2738 =
                                      let uu____2753 =
                                        let uu____2766 =
                                          let uu____2775 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____2775, (Prims.parse_int "0"),
                                            "binders")
                                           in
                                        (uu____2766, Refl_emb)  in
                                      let uu____2789 =
                                        let uu____2804 =
                                          let uu____2817 =
                                            let uu____2826 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____2826,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____2817, Refl_emb)  in
                                        [uu____2804]  in
                                      uu____2753 :: uu____2789  in
                                    uu____2702 :: uu____2738  in
                                  uu____2651 :: uu____2687  in
                                uu____2600 :: uu____2636  in
                              uu____2549 :: uu____2585  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____2534
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____2519
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____2504
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____2489
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____2474
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____2459
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____2444
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___6_3133  ->
                     match uu___6_3133 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____3208 -> failwith "Impossible") term_cs
                 in
              fun uu___7_3234  ->
                match uu___7_3234 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____3249 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____3286  ->
                   match uu____3286 with
                   | ((x,args,uu____3302),uu____3303) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____3333 =
              match uu____3333 with
              | (bv',uu____3341) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____3375 =
                let uu____3376 = FStar_Syntax_Subst.compress t3  in
                uu____3376.FStar_Syntax_Syntax.n  in
              match uu____3375 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____3385 =
                    let uu____3387 =
                      let uu____3393 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____3393  in
                    FStar_Pervasives_Native.snd uu____3387  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____3385
              | FStar_Syntax_Syntax.Tm_refine (x,uu____3414) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____3420,uu____3421) ->
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____3494 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____3494 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____3516 =
                           let uu____3517 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____3517  in
                         uu____3516.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____3535 = mk_embedding l env t0  in
                       let uu____3536 = mk_embedding l env t11  in
                       emb_arrow l uu____3535 uu____3536)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____3607 =
                      let uu____3614 =
                        let uu____3615 =
                          let uu____3630 = FStar_Syntax_Syntax.mk_Total tail1
                             in
                          ([b], uu____3630)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____3615  in
                      FStar_Syntax_Syntax.mk uu____3614  in
                    uu____3607 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____3658 ->
                  let uu____3659 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3659 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3711 =
                         let uu____3712 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____3712.FStar_Syntax_Syntax.n  in
                       (match uu____3711 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3742  ->
                                      match uu____3742 with
                                      | (t4,uu____3750) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3757 =
                              let uu____3770 =
                                FStar_Util.find_opt
                                  (fun uu____3802  ->
                                     match uu____3802 with
                                     | ((x,uu____3817,uu____3818),uu____3819)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3770 FStar_Util.must
                               in
                            (match uu____3757 with
                             | ((uu____3870,t_arity,_trepr_head),loc_embedding)
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
                        | uu____3891 ->
                            let uu____3892 =
                              let uu____3893 =
                                let uu____3895 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____3895
                                 in
                              NoTacticEmbedding uu____3893  in
                            FStar_Exn.raise uu____3892))
              | FStar_Syntax_Syntax.Tm_uinst uu____3898 ->
                  let uu____3905 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3905 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3957 =
                         let uu____3958 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____3958.FStar_Syntax_Syntax.n  in
                       (match uu____3957 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3988  ->
                                      match uu____3988 with
                                      | (t4,uu____3996) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____4003 =
                              let uu____4016 =
                                FStar_Util.find_opt
                                  (fun uu____4048  ->
                                     match uu____4048 with
                                     | ((x,uu____4063,uu____4064),uu____4065)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____4016 FStar_Util.must
                               in
                            (match uu____4003 with
                             | ((uu____4116,t_arity,_trepr_head),loc_embedding)
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
                        | uu____4137 ->
                            let uu____4138 =
                              let uu____4139 =
                                let uu____4141 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____4141
                                 in
                              NoTacticEmbedding uu____4139  in
                            FStar_Exn.raise uu____4138))
              | FStar_Syntax_Syntax.Tm_app uu____4144 ->
                  let uu____4161 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____4161 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____4213 =
                         let uu____4214 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____4214.FStar_Syntax_Syntax.n  in
                       (match uu____4213 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____4244  ->
                                      match uu____4244 with
                                      | (t4,uu____4252) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____4259 =
                              let uu____4272 =
                                FStar_Util.find_opt
                                  (fun uu____4304  ->
                                     match uu____4304 with
                                     | ((x,uu____4319,uu____4320),uu____4321)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____4272 FStar_Util.must
                               in
                            (match uu____4259 with
                             | ((uu____4372,t_arity,_trepr_head),loc_embedding)
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
                        | uu____4393 ->
                            let uu____4394 =
                              let uu____4395 =
                                let uu____4397 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____4397
                                 in
                              NoTacticEmbedding uu____4395  in
                            FStar_Exn.raise uu____4394))
              | uu____4400 ->
                  let uu____4401 =
                    let uu____4402 =
                      let uu____4404 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____4404
                       in
                    NoTacticEmbedding uu____4402  in
                  FStar_Exn.raise uu____4401
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____4426 =
                      let uu____4427 =
                        let uu____4434 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____4436 =
                          let uu____4439 =
                            let uu____4440 =
                              let uu____4441 =
                                let uu____4442 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____4442
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____4441
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____4440
                             in
                          let uu____4444 =
                            let uu____4447 =
                              let uu____4448 =
                                let uu____4449 =
                                  let uu____4450 =
                                    let uu____4457 =
                                      let uu____4460 = str_to_name "args"  in
                                      [uu____4460]  in
                                    (body, uu____4457)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____4450
                                   in
                                FStar_All.pipe_left w uu____4449  in
                              mk_lam "_" uu____4448  in
                            [uu____4447]  in
                          uu____4439 :: uu____4444  in
                        (uu____4434, uu____4436)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____4427  in
                    FStar_All.pipe_left w uu____4426  in
                  mk_lam "args" body1
              | uu____4468 ->
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
                    let uu____4517 =
                      let uu____4518 =
                        let uu____4519 =
                          let uu____4526 =
                            let uu____4529 = str_to_name "args"  in
                            [uu____4529]  in
                          (body, uu____4526)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____4519  in
                      FStar_All.pipe_left w uu____4518  in
                    (pattern, FStar_Pervasives_Native.None, uu____4517)  in
                  let default_branch =
                    let uu____4544 =
                      let uu____4545 =
                        let uu____4546 =
                          let uu____4553 = str_to_name "failwith"  in
                          let uu____4555 =
                            let uu____4558 =
                              let uu____4559 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____4559  in
                            [uu____4558]  in
                          (uu____4553, uu____4555)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____4546  in
                      FStar_All.pipe_left w uu____4545  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____4544)
                     in
                  let body1 =
                    let uu____4567 =
                      let uu____4568 =
                        let uu____4583 = str_to_name "args"  in
                        (uu____4583, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____4568  in
                    FStar_All.pipe_left w uu____4567  in
                  let body2 =
                    let uu____4620 =
                      let uu____4621 =
                        let uu____4628 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____4630 =
                          let uu____4633 =
                            let uu____4634 =
                              let uu____4635 =
                                let uu____4636 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____4636
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____4635
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____4634
                             in
                          let uu____4638 =
                            let uu____4641 = mk_lam "_" body1  in
                            [uu____4641]  in
                          uu____4633 :: uu____4638  in
                        (uu____4628, uu____4630)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____4621  in
                    FStar_All.pipe_left w uu____4620  in
                  mk_lam "args" body2
               in
            let uu____4646 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____4646 with
            | (bs,c) ->
                let uu____4679 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____4780 = FStar_Util.first_N n1 bs  in
                           match uu____4780 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____4858 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____4858
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____4875 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____4877 = FStar_Util.string_of_int n1  in
                             let uu____4879 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____4875 uu____4877 uu____4879
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____4679 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____4936 =
                       let uu____4957 =
                         FStar_Util.prefix_until
                           (fun uu____4999  ->
                              match uu____4999 with
                              | (b,uu____5008) ->
                                  let uu____5013 =
                                    let uu____5014 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____5014.FStar_Syntax_Syntax.n  in
                                  (match uu____5013 with
                                   | FStar_Syntax_Syntax.Tm_type uu____5018
                                       -> false
                                   | uu____5020 -> true)) bs1
                          in
                       match uu____4957 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____4936 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____5262 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____5262) type_vars
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
                                let uu____5362 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____5362
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____5383 =
                                      let uu____5386 =
                                        let uu____5389 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____5390 =
                                          let uu____5393 =
                                            let uu____5394 =
                                              let uu____5395 =
                                                let uu____5396 =
                                                  let uu____5408 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____5408,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____5396
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____5395
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____5394
                                             in
                                          [uu____5393; fv_lid_embedded; cb]
                                           in
                                        uu____5389 :: uu____5390  in
                                      res_embedding :: uu____5386  in
                                    FStar_List.append arg_unembeddings
                                      uu____5383
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
                                  let uu____5433 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____5433, arity, true)
                                else
                                  (let uu____5447 =
                                     let uu____5449 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____5449
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____5447
                                   then
                                     let h =
                                       let uu____5460 =
                                         let uu____5462 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____5462
                                          in
                                       str_to_top_name uu____5460  in
                                     let tac_fun =
                                       let uu____5471 =
                                         let uu____5472 =
                                           let uu____5479 =
                                             let uu____5480 =
                                               let uu____5482 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____5482
                                                in
                                             str_to_top_name uu____5480  in
                                           let uu____5490 =
                                             let uu____5493 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____5493]  in
                                           (uu____5479, uu____5490)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____5472
                                          in
                                       FStar_All.pipe_left w uu____5471  in
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
                                           let uu____5507 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____5507
                                       | uu____5511 ->
                                           let uu____5515 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____5515
                                        in
                                     let uu____5518 =
                                       let uu____5519 = mk_lam "ncb" tabs  in
                                       mk_lam "psc" uu____5519  in
                                     (uu____5518,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____5534 =
                                        let uu____5535 =
                                          let uu____5537 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____5537
                                           in
                                        NoTacticEmbedding uu____5535  in
                                      FStar_Exn.raise uu____5534))
                            | (b,uu____5549)::bs4 ->
                                let uu____5569 =
                                  let uu____5572 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____5572 :: accum_embeddings  in
                                aux loc uu____5569 bs4
                             in
                          (try
                             (fun uu___11_5594  ->
                                match () with
                                | () ->
                                    let uu____5607 = aux Syntax_term [] bs2
                                       in
                                    (match uu____5607 with
                                     | (w1,a,b) ->
                                         let uu____5635 = aux NBE_t [] bs2
                                            in
                                         (match uu____5635 with
                                          | (w',uu____5657,uu____5658) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____5694 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____5694 msg);
                                FStar_Pervasives_Native.None))))
  