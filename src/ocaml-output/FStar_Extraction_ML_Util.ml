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
    | FStar_Const.Const_range uu____75 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____105) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____111) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____116 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____120 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try (fun uu___51_134  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___50_137 ->
          let uu____138 =
            let uu____140 = FStar_Range.string_of_range p  in
            let uu____142 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____140 uu____142
             in
          failwith uu____138
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____159 =
        let uu____160 =
          let uu____161 =
            let uu____173 = FStar_Util.string_of_int i  in
            (uu____173, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____161  in
        FStar_All.pipe_right uu____160
          (fun uu____186  -> FStar_Extraction_ML_Syntax.MLE_Const uu____186)
         in
      FStar_All.pipe_right uu____159
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____195 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun uu____196  -> FStar_Extraction_ML_Syntax.MLE_Const uu____196)
         in
      FStar_All.pipe_right uu____195
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____197 =
      let uu____204 =
        let uu____207 =
          let uu____208 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____208 cstr  in
        let uu____211 =
          let uu____214 =
            let uu____215 =
              let uu____217 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____217 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____215 cint  in
          let uu____220 =
            let uu____223 =
              let uu____224 =
                let uu____226 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____226 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____224 cint  in
            let uu____229 =
              let uu____232 =
                let uu____233 =
                  let uu____235 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____235 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____233 cint  in
              let uu____238 =
                let uu____241 =
                  let uu____242 =
                    let uu____244 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____244 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____242 cint  in
                [uu____241]  in
              uu____232 :: uu____238  in
            uu____223 :: uu____229  in
          uu____214 :: uu____220  in
        uu____207 :: uu____211  in
      (mk_range_mle, uu____204)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____197
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____261 ->
          let uu____262 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____262
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____290 =
            FStar_Util.find_opt
              (fun uu____306  ->
                 match uu____306 with | (y,uu____314) -> y = x) subst
             in
          (match uu____290 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____338 =
            let uu____345 = subst_aux subst t1  in
            let uu____346 = subst_aux subst t2  in (uu____345, f, uu____346)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____338
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____353 =
            let uu____360 = FStar_List.map (subst_aux subst) args  in
            (uu____360, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____353
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____368 = FStar_List.map (subst_aux subst) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____368
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____384  ->
    fun args  ->
      match uu____384 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____398 =
               let uu____399 = FStar_List.zip formals args  in
               subst_aux uu____399 t  in
             FStar_Pervasives_Native.Some uu____398)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____431 = try_subst ts args  in
      match uu____431 with
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
    fun uu___0_448  ->
      match uu___0_448 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n) ->
          let uu____457 = FStar_Extraction_ML_UEnv.lookup_ty_const g n  in
          (match uu____457 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____463 = try_subst ts args  in
               (match uu____463 with
                | FStar_Pervasives_Native.None  ->
                    let uu____468 =
                      let uu____470 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n  in
                      let uu____472 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____474 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____470 uu____472 uu____474
                       in
                    failwith uu____468
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____481 -> FStar_Pervasives_Native.None)
      | uu____484 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____498) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____502 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___1_514  ->
    match uu___1_514 with
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
        | uu____535 ->
            let uu____540 =
              let uu____542 = FStar_Range.string_of_range r  in
              let uu____544 = eff_to_string f  in
              let uu____546 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____542
                uu____544 uu____546
               in
            failwith uu____540
  
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
    (fun uu____589  ->
       fun t  ->
         match uu____589 with
         | (uu____596,t0) ->
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
                | uu____719 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____756 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____764 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____764 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____775;
                     FStar_Extraction_ML_Syntax.loc = uu____776;_}
                   ->
                   let uu____801 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____801
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____819 = type_leq unfold_ty t2 t2'  in
                        (if uu____819
                         then
                           let body1 =
                             let uu____830 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____830
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____835 =
                             let uu____838 =
                               let uu____839 =
                                 let uu____844 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____844
                                  in
                               FStar_All.pipe_left uu____839
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____838  in
                           (true, uu____835)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____884 =
                           let uu____892 =
                             let uu____895 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun uu____898  ->
                                  FStar_Pervasives_Native.Some uu____898)
                               uu____895
                              in
                           type_leq_c unfold_ty uu____892 t2 t2'  in
                         match uu____884 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____920 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____920
                               | uu____931 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____943 ->
                   let uu____946 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____946
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____986 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____986
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____1008 = unfold_ty t  in
                 match uu____1008 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____1019 = unfold_ty t'  in
                     (match uu____1019 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____1040 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____1040
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____1064,uu____1065) ->
              let uu____1072 = unfold_ty t  in
              (match uu____1072 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____1083 -> (false, FStar_Pervasives_Native.None))
          | (uu____1090,FStar_Extraction_ML_Syntax.MLTY_Named uu____1091) ->
              let uu____1098 = unfold_ty t'  in
              (match uu____1098 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____1109 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____1120 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____1134 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____1134 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1162 =
          let uu____1169 = erase_effect_annotations t1  in
          let uu____1170 = erase_effect_annotations t2  in
          (uu____1169, FStar_Extraction_ML_Syntax.E_PURE, uu____1170)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____1162
    | uu____1171 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___2_1199  ->
    match uu___2_1199 with
    | (FStar_Util.Inl uu____1211,uu____1212)::uu____1213 -> true
    | uu____1237 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1265  ->
    match uu____1265 with
    | (ns,n) ->
        let uu____1287 =
          let uu____1289 = FStar_Util.concat_l "." (FStar_List.append ns [n])
             in
          FStar_Parser_Const.is_tuple_datacon_string uu____1289  in
        if uu____1287
        then
          let uu____1299 =
            let uu____1301 = FStar_Util.char_at n (Prims.of_int (7))  in
            FStar_Util.int_of_char uu____1301  in
          FStar_Pervasives_Native.Some uu____1299
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1320 = is_xtuple mlp  in
        (match uu____1320 with
         | FStar_Pervasives_Native.Some n ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1327 -> e)
    | uu____1331 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___3_1342  ->
    match uu___3_1342 with
    | f::uu____1349 ->
        let uu____1352 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1352 with
         | (ns,uu____1363) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____1376 -> failwith "impos"
  
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
  fun uu____1442  ->
    match uu____1442 with
    | (ns,n) ->
        let uu____1464 =
          let uu____1466 = FStar_Util.concat_l "." (FStar_List.append ns [n])
             in
          FStar_Parser_Const.is_tuple_constructor_string uu____1466  in
        if uu____1464
        then
          let uu____1476 =
            let uu____1478 = FStar_Util.char_at n (Prims.of_int (5))  in
            FStar_Util.int_of_char uu____1478  in
          FStar_Pervasives_Native.Some uu____1476
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1497 = is_xtuple_ty mlp  in
        (match uu____1497 with
         | FStar_Pervasives_Native.Some n ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1504 -> t)
    | uu____1508 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1522 = codegen_fsharp ()  in
    if uu____1522
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____1544  ->
    match uu____1544 with
    | (ns,n) ->
        let uu____1564 = codegen_fsharp ()  in
        if uu____1564
        then FStar_String.concat "." (FStar_List.append ns [n])
        else FStar_String.concat "_" (FStar_List.append ns [n])
  
let (ml_module_name_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let mlp =
      let uu____1594 =
        FStar_All.pipe_right l.FStar_Ident.ns
          (FStar_List.map (fun i  -> i.FStar_Ident.idText))
         in
      (uu____1594, ((l.FStar_Ident.ident).FStar_Ident.idText))  in
    flatten_mlpath mlp
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1625 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1625
      then true
      else
        (let uu____1632 = unfold_ty t  in
         match uu____1632 with
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
            let uu____1655 =
              let uu____1662 = eraseTypeDeep unfold_ty tyd  in
              let uu____1663 = eraseTypeDeep unfold_ty tycd  in
              (uu____1662, etag, uu____1663)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1655
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1672 = erasableType unfold_ty t  in
          if uu____1672
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1677 =
               let uu____1684 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1684, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1677)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1692 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1692
      | uu____1695 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1706 =
    let uu____1711 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1711  in
  FStar_All.pipe_left uu____1706
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
          let uu____1799 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1799
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1815 = FStar_Range.file_of_range r  in (line, uu____1815)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1838,b) ->
        let uu____1840 = doms_and_cod b  in
        (match uu____1840 with | (ds,c) -> ((a :: ds), c))
    | uu____1861 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1874 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1874
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1902,b) ->
        let uu____1904 = uncurry_mlty_fun b  in
        (match uu____1904 with | (args,res) -> ((a :: args), res))
    | uu____1925 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____1941 -> true
    | uu____1944 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____1954 -> uu____1954
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1976 =
          let uu____1982 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1982)  in
        FStar_Errors.log_issue r uu____1976
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____1995 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____2006 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____2017 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____2028 -> false
  
type wrapped_term =
  (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.mlexpr *
    Prims.int * Prims.bool)
let (interpret_plugin_as_term_fun :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ ->
        Prims.int FStar_Pervasives_Native.option ->
          FStar_Extraction_ML_Syntax.mlexpr' ->
            (FStar_Extraction_ML_Syntax.mlexpr *
              FStar_Extraction_ML_Syntax.mlexpr * Prims.int * Prims.bool)
              FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        fun arity_opt  ->
          fun ml_fv  ->
            let fv_lid =
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
            let tcenv = FStar_Extraction_ML_UEnv.tcenv_of_uenv env  in
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
              let uu____2100 =
                let uu____2101 =
                  FStar_Extraction_ML_UEnv.mlpath_of_lident env l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____2101  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2100
               in
            let lid_to_top_name l =
              let uu____2108 =
                let uu____2109 =
                  FStar_Extraction_ML_UEnv.mlpath_of_lident env l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____2109  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2108
               in
            let str_to_name s =
              let uu____2118 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____2118  in
            let str_to_top_name s =
              let uu____2127 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____2127  in
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
              let uu____2165 =
                let uu____2166 =
                  let uu____2173 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____2175 =
                    let uu____2178 =
                      let uu____2179 =
                        let uu____2180 =
                          let uu____2181 = FStar_Ident.string_of_lid fv_lid
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____2181
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____2180  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____2179
                       in
                    [uu____2178]  in
                  (uu____2173, uu____2175)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2166  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2165
               in
            let emb_prefix uu___4_2196 =
              match uu___4_2196 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____2210 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____2221 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____2250 =
                let uu____2252 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____2252  in
              emb_prefix l uu____2250  in
            let mk_any_embedding l s =
              let uu____2268 =
                let uu____2269 =
                  let uu____2276 = emb_prefix l "mk_any_emb"  in
                  let uu____2278 =
                    let uu____2281 = str_to_name s  in [uu____2281]  in
                  (uu____2276, uu____2278)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2269  in
              FStar_All.pipe_left w uu____2268  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____2331 =
                let uu____2332 =
                  let uu____2339 = emb_prefix l "e_arrow"  in
                  (uu____2339, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2332  in
              FStar_All.pipe_left w uu____2331  in
            let known_type_constructors =
              let term_cs =
                let uu____2377 =
                  let uu____2392 =
                    let uu____2407 =
                      let uu____2422 =
                        let uu____2437 =
                          let uu____2452 =
                            let uu____2467 =
                              let uu____2482 =
                                let uu____2495 =
                                  let uu____2504 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.of_int (2))
                                      FStar_Range.dummyRange
                                     in
                                  (uu____2504, (Prims.of_int (2)), "tuple2")
                                   in
                                (uu____2495, Syntax_term)  in
                              let uu____2518 =
                                let uu____2533 =
                                  let uu____2546 =
                                    let uu____2555 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____2555, Prims.int_zero, "term")  in
                                  (uu____2546, Refl_emb)  in
                                let uu____2569 =
                                  let uu____2584 =
                                    let uu____2597 =
                                      let uu____2606 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "sigelt"
                                         in
                                      (uu____2606, Prims.int_zero, "sigelt")
                                       in
                                    (uu____2597, Refl_emb)  in
                                  let uu____2620 =
                                    let uu____2635 =
                                      let uu____2648 =
                                        let uu____2657 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "fv"
                                           in
                                        (uu____2657, Prims.int_zero, "fv")
                                         in
                                      (uu____2648, Refl_emb)  in
                                    let uu____2671 =
                                      let uu____2686 =
                                        let uu____2699 =
                                          let uu____2708 =
                                            FStar_Reflection_Data.fstar_refl_types_lid
                                              "binder"
                                             in
                                          (uu____2708, Prims.int_zero,
                                            "binder")
                                           in
                                        (uu____2699, Refl_emb)  in
                                      let uu____2722 =
                                        let uu____2737 =
                                          let uu____2750 =
                                            let uu____2759 =
                                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                                "binders"
                                               in
                                            (uu____2759, Prims.int_zero,
                                              "binders")
                                             in
                                          (uu____2750, Refl_emb)  in
                                        let uu____2773 =
                                          let uu____2788 =
                                            let uu____2801 =
                                              let uu____2810 =
                                                FStar_Reflection_Data.fstar_refl_data_lid
                                                  "exp"
                                                 in
                                              (uu____2810, Prims.int_zero,
                                                "exp")
                                               in
                                            (uu____2801, Refl_emb)  in
                                          [uu____2788]  in
                                        uu____2737 :: uu____2773  in
                                      uu____2686 :: uu____2722  in
                                    uu____2635 :: uu____2671  in
                                  uu____2584 :: uu____2620  in
                                uu____2533 :: uu____2569  in
                              uu____2482 :: uu____2518  in
                            ((FStar_Parser_Const.option_lid, Prims.int_one,
                               "option"), Syntax_term)
                              :: uu____2467
                             in
                          ((FStar_Parser_Const.list_lid, Prims.int_one,
                             "list"), Syntax_term)
                            :: uu____2452
                           in
                        ((FStar_Parser_Const.norm_step_lid, Prims.int_zero,
                           "norm_step"), Syntax_term)
                          :: uu____2437
                         in
                      ((FStar_Parser_Const.string_lid, Prims.int_zero,
                         "string"), Syntax_term)
                        :: uu____2422
                       in
                    ((FStar_Parser_Const.unit_lid, Prims.int_zero, "unit"),
                      Syntax_term) :: uu____2407
                     in
                  ((FStar_Parser_Const.bool_lid, Prims.int_zero, "bool"),
                    Syntax_term) :: uu____2392
                   in
                ((FStar_Parser_Const.int_lid, Prims.int_zero, "int"),
                  Syntax_term) :: uu____2377
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___5_3129  ->
                     match uu___5_3129 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____3204 -> failwith "Impossible") term_cs
                 in
              fun uu___6_3230  ->
                match uu___6_3230 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____3245 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n =
              FStar_Util.for_some
                (fun uu____3282  ->
                   match uu____3282 with
                   | ((x,args,uu____3298),uu____3299) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____3329 =
              match uu____3329 with
              | (bv',uu____3337) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env1 t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____3371 =
                let uu____3372 = FStar_Syntax_Subst.compress t3  in
                uu____3372.FStar_Syntax_Syntax.n  in
              match uu____3371 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env1 ->
                  let uu____3381 =
                    let uu____3383 =
                      let uu____3389 =
                        FStar_Util.find_opt (find_env_entry bv) env1  in
                      FStar_Util.must uu____3389  in
                    FStar_Pervasives_Native.snd uu____3383  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____3381
              | FStar_Syntax_Syntax.Tm_refine (x,uu____3410) ->
                  mk_embedding l env1 x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____3416,uu____3417) ->
                  mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____3490 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____3490 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____3512 =
                           let uu____3513 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____3513  in
                         uu____3512.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____3531 = mk_embedding l env1 t0  in
                       let uu____3532 = mk_embedding l env1 t11  in
                       emb_arrow l uu____3531 uu____3532)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____3603 =
                      let uu____3610 =
                        let uu____3611 =
                          let uu____3626 = FStar_Syntax_Syntax.mk_Total tail
                             in
                          ([b], uu____3626)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____3611  in
                      FStar_Syntax_Syntax.mk uu____3610  in
                    uu____3603 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_fvar uu____3651 ->
                  let uu____3652 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3652 with
                   | (head,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3704 =
                         let uu____3705 = FStar_Syntax_Util.un_uinst head  in
                         uu____3705.FStar_Syntax_Syntax.n  in
                       (match uu____3704 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3731  ->
                                      match uu____3731 with
                                      | (t4,uu____3739) ->
                                          mk_embedding l env1 t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3746 =
                              let uu____3759 =
                                FStar_Util.find_opt
                                  (fun uu____3791  ->
                                     match uu____3791 with
                                     | ((x,uu____3806,uu____3807),uu____3808)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3759 FStar_Util.must
                               in
                            (match uu____3746 with
                             | ((uu____3859,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | uu____3876 when
                                      uu____3876 = Prims.int_zero -> head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu____3881 ->
                            let uu____3882 =
                              let uu____3883 =
                                let uu____3885 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____3885
                                 in
                              NoTacticEmbedding uu____3883  in
                            FStar_Exn.raise uu____3882))
              | FStar_Syntax_Syntax.Tm_uinst uu____3888 ->
                  let uu____3895 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3895 with
                   | (head,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3947 =
                         let uu____3948 = FStar_Syntax_Util.un_uinst head  in
                         uu____3948.FStar_Syntax_Syntax.n  in
                       (match uu____3947 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3974  ->
                                      match uu____3974 with
                                      | (t4,uu____3982) ->
                                          mk_embedding l env1 t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3989 =
                              let uu____4002 =
                                FStar_Util.find_opt
                                  (fun uu____4034  ->
                                     match uu____4034 with
                                     | ((x,uu____4049,uu____4050),uu____4051)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____4002 FStar_Util.must
                               in
                            (match uu____3989 with
                             | ((uu____4102,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | uu____4119 when
                                      uu____4119 = Prims.int_zero -> head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu____4124 ->
                            let uu____4125 =
                              let uu____4126 =
                                let uu____4128 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____4128
                                 in
                              NoTacticEmbedding uu____4126  in
                            FStar_Exn.raise uu____4125))
              | FStar_Syntax_Syntax.Tm_app uu____4131 ->
                  let uu____4148 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____4148 with
                   | (head,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____4200 =
                         let uu____4201 = FStar_Syntax_Util.un_uinst head  in
                         uu____4201.FStar_Syntax_Syntax.n  in
                       (match uu____4200 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____4227  ->
                                      match uu____4227 with
                                      | (t4,uu____4235) ->
                                          mk_embedding l env1 t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____4242 =
                              let uu____4255 =
                                FStar_Util.find_opt
                                  (fun uu____4287  ->
                                     match uu____4287 with
                                     | ((x,uu____4302,uu____4303),uu____4304)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____4255 FStar_Util.must
                               in
                            (match uu____4242 with
                             | ((uu____4355,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | uu____4372 when
                                      uu____4372 = Prims.int_zero -> head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu____4377 ->
                            let uu____4378 =
                              let uu____4379 =
                                let uu____4381 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____4381
                                 in
                              NoTacticEmbedding uu____4379  in
                            FStar_Exn.raise uu____4378))
              | uu____4384 ->
                  let uu____4385 =
                    let uu____4386 =
                      let uu____4388 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____4388
                       in
                    NoTacticEmbedding uu____4386  in
                  FStar_Exn.raise uu____4385
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____4410 =
                      let uu____4411 =
                        let uu____4418 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____4420 =
                          let uu____4423 =
                            let uu____4424 =
                              let uu____4425 =
                                let uu____4426 =
                                  FStar_Ident.string_of_lid fv_lid  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____4426
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____4425
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____4424
                             in
                          let uu____4428 =
                            let uu____4431 =
                              let uu____4432 =
                                let uu____4433 =
                                  let uu____4434 =
                                    let uu____4441 =
                                      let uu____4444 = str_to_name "args"  in
                                      [uu____4444]  in
                                    (body, uu____4441)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____4434
                                   in
                                FStar_All.pipe_left w uu____4433  in
                              mk_lam "_" uu____4432  in
                            [uu____4431]  in
                          uu____4423 :: uu____4428  in
                        (uu____4418, uu____4420)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____4411  in
                    FStar_All.pipe_left w uu____4410  in
                  mk_lam "args" body1
              | uu____4452 ->
                  let args_tail =
                    FStar_Extraction_ML_Syntax.MLP_Var "args_tail"  in
                  let mk_cons hd_pat tail_pat =
                    FStar_Extraction_ML_Syntax.MLP_CTor
                      ((["Prims"], "Cons"), [hd_pat; tail_pat])
                     in
                  let fst_pat v =
                    FStar_Extraction_ML_Syntax.MLP_Tuple
                      [FStar_Extraction_ML_Syntax.MLP_Var v;
                      FStar_Extraction_ML_Syntax.MLP_Wild]
                     in
                  let pattern =
                    FStar_List.fold_right
                      (fun hd_var  -> mk_cons (fst_pat hd_var)) tvar_names
                      args_tail
                     in
                  let branch =
                    let uu____4501 =
                      let uu____4502 =
                        let uu____4503 =
                          let uu____4510 =
                            let uu____4513 = str_to_name "args"  in
                            [uu____4513]  in
                          (body, uu____4510)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____4503  in
                      FStar_All.pipe_left w uu____4502  in
                    (pattern, FStar_Pervasives_Native.None, uu____4501)  in
                  let default_branch =
                    let uu____4528 =
                      let uu____4529 =
                        let uu____4530 =
                          let uu____4537 = str_to_name "failwith"  in
                          let uu____4539 =
                            let uu____4542 =
                              let uu____4543 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____4543  in
                            [uu____4542]  in
                          (uu____4537, uu____4539)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____4530  in
                      FStar_All.pipe_left w uu____4529  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____4528)
                     in
                  let body1 =
                    let uu____4551 =
                      let uu____4552 =
                        let uu____4567 = str_to_name "args"  in
                        (uu____4567, [branch; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____4552  in
                    FStar_All.pipe_left w uu____4551  in
                  let body2 =
                    let uu____4604 =
                      let uu____4605 =
                        let uu____4612 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____4614 =
                          let uu____4617 =
                            let uu____4618 =
                              let uu____4619 =
                                let uu____4620 =
                                  FStar_Ident.string_of_lid fv_lid  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____4620
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____4619
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____4618
                             in
                          let uu____4622 =
                            let uu____4625 = mk_lam "_" body1  in
                            [uu____4625]  in
                          uu____4617 :: uu____4622  in
                        (uu____4612, uu____4614)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____4605  in
                    FStar_All.pipe_left w uu____4604  in
                  mk_lam "args" body2
               in
            let uu____4630 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____4630 with
            | (bs,c) ->
                let uu____4639 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n ->
                      let n_bs = FStar_List.length bs  in
                      if n = n_bs
                      then (bs, c)
                      else
                        if n < n_bs
                        then
                          (let uu____4732 = FStar_Util.first_N n bs  in
                           match uu____4732 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____4810 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____4810
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____4827 =
                               FStar_Ident.string_of_lid fv_lid  in
                             let uu____4829 = FStar_Util.string_of_int n  in
                             let uu____4831 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____4827 uu____4829 uu____4831
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____4639 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____4882 =
                       let uu____4903 =
                         FStar_Util.prefix_until
                           (fun uu____4945  ->
                              match uu____4945 with
                              | (b,uu____4954) ->
                                  let uu____4959 =
                                    let uu____4960 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____4960.FStar_Syntax_Syntax.n  in
                                  (match uu____4959 with
                                   | FStar_Syntax_Syntax.Tm_type uu____4964
                                       -> false
                                   | uu____4966 -> true)) bs1
                          in
                       match uu____4903 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____4882 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____5208 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____5208) type_vars
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
                                let fv_lid1 =
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                let uu____5308 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____5308
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____5325 =
                                      let uu____5328 =
                                        let uu____5331 =
                                          lid_to_top_name fv_lid1  in
                                        let uu____5332 =
                                          let uu____5335 =
                                            let uu____5336 =
                                              let uu____5337 =
                                                let uu____5338 =
                                                  let uu____5350 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____5350,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____5338
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____5337
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____5336
                                             in
                                          [uu____5335; fv_lid_embedded; cb]
                                           in
                                        uu____5331 :: uu____5332  in
                                      res_embedding :: uu____5328  in
                                    FStar_List.append arg_unembeddings
                                      uu____5325
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
                                  let uu____5369 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____5369, arity, true)
                                else
                                  (let uu____5379 =
                                     let uu____5381 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____5381
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____5379
                                   then
                                     let h =
                                       let uu____5392 =
                                         let uu____5394 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____5394
                                          in
                                       str_to_top_name uu____5392  in
                                     let tac_fun =
                                       let uu____5397 =
                                         let uu____5398 =
                                           let uu____5405 =
                                             let uu____5406 =
                                               let uu____5408 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____5408
                                                in
                                             str_to_top_name uu____5406  in
                                           let uu____5410 =
                                             let uu____5413 =
                                               lid_to_top_name fv_lid1  in
                                             [uu____5413]  in
                                           (uu____5405, uu____5410)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____5398
                                          in
                                       FStar_All.pipe_left w uu____5397  in
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
                                           let uu____5427 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____5427
                                       | uu____5431 ->
                                           let uu____5435 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____5435
                                        in
                                     let uu____5438 =
                                       let uu____5439 = mk_lam "ncb" tabs  in
                                       mk_lam "psc" uu____5439  in
                                     (uu____5438, (arity + Prims.int_one),
                                       false)
                                   else
                                     (let uu____5448 =
                                        let uu____5449 =
                                          let uu____5451 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____5451
                                           in
                                        NoTacticEmbedding uu____5449  in
                                      FStar_Exn.raise uu____5448))
                            | (b,uu____5463)::bs4 ->
                                let uu____5483 =
                                  let uu____5486 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____5486 :: accum_embeddings  in
                                aux loc uu____5483 bs4
                             in
                          (try
                             (fun uu___688_5508  ->
                                match () with
                                | () ->
                                    let uu____5521 = aux Syntax_term [] bs2
                                       in
                                    (match uu____5521 with
                                     | (w1,a,b) ->
                                         let uu____5549 = aux NBE_t [] bs2
                                            in
                                         (match uu____5549 with
                                          | (w',uu____5571,uu____5572) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____5608 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____5608 msg);
                                FStar_Pervasives_Native.None))))
  