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
    | FStar_Const.Const_string (s,uu____113) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____118 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____122 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try (fun uu___51_136  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___50_139 ->
          let uu____140 =
            let uu____142 = FStar_Range.string_of_range p  in
            let uu____144 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____142 uu____144
             in
          failwith uu____140
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____161 =
        let uu____162 =
          let uu____163 =
            let uu____175 = FStar_Util.string_of_int i  in
            (uu____175, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____163  in
        FStar_All.pipe_right uu____162
          (fun uu____188  -> FStar_Extraction_ML_Syntax.MLE_Const uu____188)
         in
      FStar_All.pipe_right uu____161
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____197 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun uu____198  -> FStar_Extraction_ML_Syntax.MLE_Const uu____198)
         in
      FStar_All.pipe_right uu____197
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____199 =
      let uu____206 =
        let uu____209 =
          let uu____210 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____210 cstr  in
        let uu____213 =
          let uu____216 =
            let uu____217 =
              let uu____219 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____219 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____217 cint  in
          let uu____222 =
            let uu____225 =
              let uu____226 =
                let uu____228 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____228 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____226 cint  in
            let uu____231 =
              let uu____234 =
                let uu____235 =
                  let uu____237 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____237 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____235 cint  in
              let uu____240 =
                let uu____243 =
                  let uu____244 =
                    let uu____246 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____246 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____244 cint  in
                [uu____243]  in
              uu____234 :: uu____240  in
            uu____225 :: uu____231  in
          uu____216 :: uu____222  in
        uu____209 :: uu____213  in
      (mk_range_mle, uu____206)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____199
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____263 ->
          let uu____264 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____264
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____292 =
            FStar_Util.find_opt
              (fun uu____308  ->
                 match uu____308 with | (y,uu____316) -> y = x) subst
             in
          (match uu____292 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____340 =
            let uu____347 = subst_aux subst t1  in
            let uu____348 = subst_aux subst t2  in (uu____347, f, uu____348)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____340
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____355 =
            let uu____362 = FStar_List.map (subst_aux subst) args  in
            (uu____362, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____355
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____370 = FStar_List.map (subst_aux subst) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____370
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____386  ->
    fun args  ->
      match uu____386 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____400 =
               let uu____401 = FStar_List.zip formals args  in
               subst_aux uu____401 t  in
             FStar_Pervasives_Native.Some uu____400)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____433 = try_subst ts args  in
      match uu____433 with
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
    fun uu___0_450  ->
      match uu___0_450 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n) ->
          let uu____459 = FStar_Extraction_ML_UEnv.lookup_ty_const g n  in
          (match uu____459 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____465 = try_subst ts args  in
               (match uu____465 with
                | FStar_Pervasives_Native.None  ->
                    let uu____470 =
                      let uu____472 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n  in
                      let uu____474 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____476 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____472 uu____474 uu____476
                       in
                    failwith uu____470
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____483 -> FStar_Pervasives_Native.None)
      | uu____486 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____500) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____504 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___1_516  ->
    match uu___1_516 with
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
        | uu____537 ->
            let uu____542 =
              let uu____544 = FStar_Range.string_of_range r  in
              let uu____546 = eff_to_string f  in
              let uu____548 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____544
                uu____546 uu____548
               in
            failwith uu____542
  
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
    (fun uu____591  ->
       fun t  ->
         match uu____591 with
         | (uu____598,t0) ->
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
                | uu____721 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____758 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____766 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____766 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____777;
                     FStar_Extraction_ML_Syntax.loc = uu____778;_}
                   ->
                   let uu____803 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____803
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____821 = type_leq unfold_ty t2 t2'  in
                        (if uu____821
                         then
                           let body1 =
                             let uu____832 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____832
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____837 =
                             let uu____840 =
                               let uu____841 =
                                 let uu____846 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____846
                                  in
                               FStar_All.pipe_left uu____841
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____840  in
                           (true, uu____837)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____886 =
                           let uu____894 =
                             let uu____897 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun uu____900  ->
                                  FStar_Pervasives_Native.Some uu____900)
                               uu____897
                              in
                           type_leq_c unfold_ty uu____894 t2 t2'  in
                         match uu____886 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____922 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____922
                               | uu____933 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____945 ->
                   let uu____948 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____948
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____988 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____988
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____1010 = unfold_ty t  in
                 match uu____1010 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____1021 = unfold_ty t'  in
                     (match uu____1021 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____1042 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____1042
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____1066,uu____1067) ->
              let uu____1074 = unfold_ty t  in
              (match uu____1074 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____1085 -> (false, FStar_Pervasives_Native.None))
          | (uu____1092,FStar_Extraction_ML_Syntax.MLTY_Named uu____1093) ->
              let uu____1100 = unfold_ty t'  in
              (match uu____1100 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____1111 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____1122 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____1136 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____1136 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1164 =
          let uu____1171 = erase_effect_annotations t1  in
          let uu____1172 = erase_effect_annotations t2  in
          (uu____1171, FStar_Extraction_ML_Syntax.E_PURE, uu____1172)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____1164
    | uu____1173 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___2_1201  ->
    match uu___2_1201 with
    | (FStar_Util.Inl uu____1213,uu____1214)::uu____1215 -> true
    | uu____1239 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1267  ->
    match uu____1267 with
    | (ns,n) ->
        let uu____1289 =
          let uu____1291 = FStar_Util.concat_l "." (FStar_List.append ns [n])
             in
          FStar_Parser_Const.is_tuple_datacon_string uu____1291  in
        if uu____1289
        then
          let uu____1301 =
            let uu____1303 = FStar_Util.char_at n (Prims.of_int (7))  in
            FStar_Util.int_of_char uu____1303  in
          FStar_Pervasives_Native.Some uu____1301
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1322 = is_xtuple mlp  in
        (match uu____1322 with
         | FStar_Pervasives_Native.Some n ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1329 -> e)
    | uu____1333 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___3_1344  ->
    match uu___3_1344 with
    | f::uu____1351 ->
        let uu____1354 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1354 with
         | (ns,uu____1365) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____1378 -> failwith "impos"
  
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
  fun uu____1444  ->
    match uu____1444 with
    | (ns,n) ->
        let uu____1466 =
          let uu____1468 = FStar_Util.concat_l "." (FStar_List.append ns [n])
             in
          FStar_Parser_Const.is_tuple_constructor_string uu____1468  in
        if uu____1466
        then
          let uu____1478 =
            let uu____1480 = FStar_Util.char_at n (Prims.of_int (5))  in
            FStar_Util.int_of_char uu____1480  in
          FStar_Pervasives_Native.Some uu____1478
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1499 = is_xtuple_ty mlp  in
        (match uu____1499 with
         | FStar_Pervasives_Native.Some n ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1506 -> t)
    | uu____1510 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1524 = codegen_fsharp ()  in
    if uu____1524
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____1546  ->
    match uu____1546 with
    | (ns,n) ->
        let uu____1566 = codegen_fsharp ()  in
        if uu____1566
        then FStar_String.concat "." (FStar_List.append ns [n])
        else FStar_String.concat "_" (FStar_List.append ns [n])
  
let (ml_module_name_of_lid : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let mlp =
      let uu____1596 =
        FStar_All.pipe_right l.FStar_Ident.ns
          (FStar_List.map (fun i  -> i.FStar_Ident.idText))
         in
      (uu____1596, ((l.FStar_Ident.ident).FStar_Ident.idText))  in
    flatten_mlpath mlp
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1627 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1627
      then true
      else
        (let uu____1634 = unfold_ty t  in
         match uu____1634 with
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
            let uu____1657 =
              let uu____1664 = eraseTypeDeep unfold_ty tyd  in
              let uu____1665 = eraseTypeDeep unfold_ty tycd  in
              (uu____1664, etag, uu____1665)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1657
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1674 = erasableType unfold_ty t  in
          if uu____1674
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1679 =
               let uu____1686 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1686, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1679)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1694 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1694
      | uu____1697 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1708 =
    let uu____1713 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1713  in
  FStar_All.pipe_left uu____1708
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
          let uu____1801 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1801
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1817 = FStar_Range.file_of_range r  in (line, uu____1817)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1840,b) ->
        let uu____1842 = doms_and_cod b  in
        (match uu____1842 with | (ds,c) -> ((a :: ds), c))
    | uu____1863 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1876 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1876
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1904,b) ->
        let uu____1906 = uncurry_mlty_fun b  in
        (match uu____1906 with | (args,res) -> ((a :: args), res))
    | uu____1927 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____1943 -> true
    | uu____1946 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____1956 -> uu____1956
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1978 =
          let uu____1984 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1984)  in
        FStar_Errors.log_issue r uu____1978
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____1997 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____2008 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____2019 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____2030 -> false
  
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
              let uu____2102 =
                let uu____2103 =
                  FStar_Extraction_ML_UEnv.mlpath_of_lident env l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____2103  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2102
               in
            let lid_to_top_name l =
              let uu____2110 =
                let uu____2111 =
                  FStar_Extraction_ML_UEnv.mlpath_of_lident env l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____2111  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2110
               in
            let str_to_name s =
              let uu____2120 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____2120  in
            let str_to_top_name s =
              let uu____2129 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____2129  in
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
              let uu____2167 =
                let uu____2168 =
                  let uu____2175 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____2177 =
                    let uu____2180 =
                      let uu____2181 =
                        let uu____2182 =
                          let uu____2183 = FStar_Ident.string_of_lid fv_lid
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____2183
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____2182  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____2181
                       in
                    [uu____2180]  in
                  (uu____2175, uu____2177)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2168  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2167
               in
            let emb_prefix uu___4_2198 =
              match uu___4_2198 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____2212 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____2223 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____2252 =
                let uu____2254 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____2254  in
              emb_prefix l uu____2252  in
            let mk_any_embedding l s =
              let uu____2270 =
                let uu____2271 =
                  let uu____2278 = emb_prefix l "mk_any_emb"  in
                  let uu____2280 =
                    let uu____2283 = str_to_name s  in [uu____2283]  in
                  (uu____2278, uu____2280)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2271  in
              FStar_All.pipe_left w uu____2270  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____2333 =
                let uu____2334 =
                  let uu____2341 = emb_prefix l "e_arrow"  in
                  (uu____2341, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____2334  in
              FStar_All.pipe_left w uu____2333  in
            let known_type_constructors =
              let term_cs =
                let uu____2379 =
                  let uu____2394 =
                    let uu____2409 =
                      let uu____2424 =
                        let uu____2439 =
                          let uu____2454 =
                            let uu____2469 =
                              let uu____2484 =
                                let uu____2497 =
                                  let uu____2506 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.of_int (2))
                                      FStar_Range.dummyRange
                                     in
                                  (uu____2506, (Prims.of_int (2)), "tuple2")
                                   in
                                (uu____2497, Syntax_term)  in
                              let uu____2520 =
                                let uu____2535 =
                                  let uu____2548 =
                                    let uu____2557 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____2557, Prims.int_zero, "term")  in
                                  (uu____2548, Refl_emb)  in
                                let uu____2571 =
                                  let uu____2586 =
                                    let uu____2599 =
                                      let uu____2608 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "sigelt"
                                         in
                                      (uu____2608, Prims.int_zero, "sigelt")
                                       in
                                    (uu____2599, Refl_emb)  in
                                  let uu____2622 =
                                    let uu____2637 =
                                      let uu____2650 =
                                        let uu____2659 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "fv"
                                           in
                                        (uu____2659, Prims.int_zero, "fv")
                                         in
                                      (uu____2650, Refl_emb)  in
                                    let uu____2673 =
                                      let uu____2688 =
                                        let uu____2701 =
                                          let uu____2710 =
                                            FStar_Reflection_Data.fstar_refl_types_lid
                                              "binder"
                                             in
                                          (uu____2710, Prims.int_zero,
                                            "binder")
                                           in
                                        (uu____2701, Refl_emb)  in
                                      let uu____2724 =
                                        let uu____2739 =
                                          let uu____2752 =
                                            let uu____2761 =
                                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                                "binders"
                                               in
                                            (uu____2761, Prims.int_zero,
                                              "binders")
                                             in
                                          (uu____2752, Refl_emb)  in
                                        let uu____2775 =
                                          let uu____2790 =
                                            let uu____2803 =
                                              let uu____2812 =
                                                FStar_Reflection_Data.fstar_refl_data_lid
                                                  "exp"
                                                 in
                                              (uu____2812, Prims.int_zero,
                                                "exp")
                                               in
                                            (uu____2803, Refl_emb)  in
                                          [uu____2790]  in
                                        uu____2739 :: uu____2775  in
                                      uu____2688 :: uu____2724  in
                                    uu____2637 :: uu____2673  in
                                  uu____2586 :: uu____2622  in
                                uu____2535 :: uu____2571  in
                              uu____2484 :: uu____2520  in
                            ((FStar_Parser_Const.option_lid, Prims.int_one,
                               "option"), Syntax_term)
                              :: uu____2469
                             in
                          ((FStar_Parser_Const.list_lid, Prims.int_one,
                             "list"), Syntax_term)
                            :: uu____2454
                           in
                        ((FStar_Parser_Const.norm_step_lid, Prims.int_zero,
                           "norm_step"), Syntax_term)
                          :: uu____2439
                         in
                      ((FStar_Parser_Const.string_lid, Prims.int_zero,
                         "string"), Syntax_term)
                        :: uu____2424
                       in
                    ((FStar_Parser_Const.unit_lid, Prims.int_zero, "unit"),
                      Syntax_term) :: uu____2409
                     in
                  ((FStar_Parser_Const.bool_lid, Prims.int_zero, "bool"),
                    Syntax_term) :: uu____2394
                   in
                ((FStar_Parser_Const.int_lid, Prims.int_zero, "int"),
                  Syntax_term) :: uu____2379
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___5_3131  ->
                     match uu___5_3131 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____3206 -> failwith "Impossible") term_cs
                 in
              fun uu___6_3232  ->
                match uu___6_3232 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____3247 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n =
              FStar_Util.for_some
                (fun uu____3284  ->
                   match uu____3284 with
                   | ((x,args,uu____3300),uu____3301) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____3331 =
              match uu____3331 with
              | (bv',uu____3339) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env1 t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____3373 =
                let uu____3374 = FStar_Syntax_Subst.compress t3  in
                uu____3374.FStar_Syntax_Syntax.n  in
              match uu____3373 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env1 ->
                  let uu____3383 =
                    let uu____3385 =
                      let uu____3391 =
                        FStar_Util.find_opt (find_env_entry bv) env1  in
                      FStar_Util.must uu____3391  in
                    FStar_Pervasives_Native.snd uu____3385  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____3383
              | FStar_Syntax_Syntax.Tm_refine (x,uu____3412) ->
                  mk_embedding l env1 x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____3418,uu____3419) ->
                  mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____3492 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____3492 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____3514 =
                           let uu____3515 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____3515  in
                         uu____3514.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____3533 = mk_embedding l env1 t0  in
                       let uu____3534 = mk_embedding l env1 t11  in
                       emb_arrow l uu____3533 uu____3534)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____3605 =
                      let uu____3612 =
                        let uu____3613 =
                          let uu____3628 = FStar_Syntax_Syntax.mk_Total tail
                             in
                          ([b], uu____3628)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____3613  in
                      FStar_Syntax_Syntax.mk uu____3612  in
                    uu____3605 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env1 t4
              | FStar_Syntax_Syntax.Tm_fvar uu____3653 ->
                  let uu____3654 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3654 with
                   | (head,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3706 =
                         let uu____3707 = FStar_Syntax_Util.un_uinst head  in
                         uu____3707.FStar_Syntax_Syntax.n  in
                       (match uu____3706 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3733  ->
                                      match uu____3733 with
                                      | (t4,uu____3741) ->
                                          mk_embedding l env1 t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3748 =
                              let uu____3761 =
                                FStar_Util.find_opt
                                  (fun uu____3793  ->
                                     match uu____3793 with
                                     | ((x,uu____3808,uu____3809),uu____3810)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3761 FStar_Util.must
                               in
                            (match uu____3748 with
                             | ((uu____3861,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | uu____3878 when
                                      uu____3878 = Prims.int_zero -> head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu____3883 ->
                            let uu____3884 =
                              let uu____3885 =
                                let uu____3887 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____3887
                                 in
                              NoTacticEmbedding uu____3885  in
                            FStar_Exn.raise uu____3884))
              | FStar_Syntax_Syntax.Tm_uinst uu____3890 ->
                  let uu____3897 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3897 with
                   | (head,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3949 =
                         let uu____3950 = FStar_Syntax_Util.un_uinst head  in
                         uu____3950.FStar_Syntax_Syntax.n  in
                       (match uu____3949 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3976  ->
                                      match uu____3976 with
                                      | (t4,uu____3984) ->
                                          mk_embedding l env1 t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3991 =
                              let uu____4004 =
                                FStar_Util.find_opt
                                  (fun uu____4036  ->
                                     match uu____4036 with
                                     | ((x,uu____4051,uu____4052),uu____4053)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____4004 FStar_Util.must
                               in
                            (match uu____3991 with
                             | ((uu____4104,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | uu____4121 when
                                      uu____4121 = Prims.int_zero -> head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu____4126 ->
                            let uu____4127 =
                              let uu____4128 =
                                let uu____4130 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____4130
                                 in
                              NoTacticEmbedding uu____4128  in
                            FStar_Exn.raise uu____4127))
              | FStar_Syntax_Syntax.Tm_app uu____4133 ->
                  let uu____4150 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____4150 with
                   | (head,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____4202 =
                         let uu____4203 = FStar_Syntax_Util.un_uinst head  in
                         uu____4203.FStar_Syntax_Syntax.n  in
                       (match uu____4202 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____4229  ->
                                      match uu____4229 with
                                      | (t4,uu____4237) ->
                                          mk_embedding l env1 t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____4244 =
                              let uu____4257 =
                                FStar_Util.find_opt
                                  (fun uu____4289  ->
                                     match uu____4289 with
                                     | ((x,uu____4304,uu____4305),uu____4306)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____4257 FStar_Util.must
                               in
                            (match uu____4244 with
                             | ((uu____4357,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head1 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | uu____4374 when
                                      uu____4374 = Prims.int_zero -> head1
                                  | n ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head1, arg_embeddings))))
                        | uu____4379 ->
                            let uu____4380 =
                              let uu____4381 =
                                let uu____4383 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____4383
                                 in
                              NoTacticEmbedding uu____4381  in
                            FStar_Exn.raise uu____4380))
              | uu____4386 ->
                  let uu____4387 =
                    let uu____4388 =
                      let uu____4390 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____4390
                       in
                    NoTacticEmbedding uu____4388  in
                  FStar_Exn.raise uu____4387
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____4412 =
                      let uu____4413 =
                        let uu____4420 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____4422 =
                          let uu____4425 =
                            let uu____4426 =
                              let uu____4427 =
                                let uu____4428 =
                                  FStar_Ident.string_of_lid fv_lid  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____4428
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____4427
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____4426
                             in
                          let uu____4430 =
                            let uu____4433 =
                              let uu____4434 =
                                let uu____4435 =
                                  let uu____4436 =
                                    let uu____4443 =
                                      let uu____4446 = str_to_name "args"  in
                                      [uu____4446]  in
                                    (body, uu____4443)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____4436
                                   in
                                FStar_All.pipe_left w uu____4435  in
                              mk_lam "_" uu____4434  in
                            [uu____4433]  in
                          uu____4425 :: uu____4430  in
                        (uu____4420, uu____4422)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____4413  in
                    FStar_All.pipe_left w uu____4412  in
                  mk_lam "args" body1
              | uu____4454 ->
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
                    let uu____4503 =
                      let uu____4504 =
                        let uu____4505 =
                          let uu____4512 =
                            let uu____4515 = str_to_name "args"  in
                            [uu____4515]  in
                          (body, uu____4512)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____4505  in
                      FStar_All.pipe_left w uu____4504  in
                    (pattern, FStar_Pervasives_Native.None, uu____4503)  in
                  let default_branch =
                    let uu____4530 =
                      let uu____4531 =
                        let uu____4532 =
                          let uu____4539 = str_to_name "failwith"  in
                          let uu____4541 =
                            let uu____4544 =
                              let uu____4545 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____4545  in
                            [uu____4544]  in
                          (uu____4539, uu____4541)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____4532  in
                      FStar_All.pipe_left w uu____4531  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____4530)
                     in
                  let body1 =
                    let uu____4553 =
                      let uu____4554 =
                        let uu____4569 = str_to_name "args"  in
                        (uu____4569, [branch; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____4554  in
                    FStar_All.pipe_left w uu____4553  in
                  let body2 =
                    let uu____4606 =
                      let uu____4607 =
                        let uu____4614 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____4616 =
                          let uu____4619 =
                            let uu____4620 =
                              let uu____4621 =
                                let uu____4622 =
                                  FStar_Ident.string_of_lid fv_lid  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____4622
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____4621
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____4620
                             in
                          let uu____4624 =
                            let uu____4627 = mk_lam "_" body1  in
                            [uu____4627]  in
                          uu____4619 :: uu____4624  in
                        (uu____4614, uu____4616)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____4607  in
                    FStar_All.pipe_left w uu____4606  in
                  mk_lam "args" body2
               in
            let uu____4632 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____4632 with
            | (bs,c) ->
                let uu____4641 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n ->
                      let n_bs = FStar_List.length bs  in
                      if n = n_bs
                      then (bs, c)
                      else
                        if n < n_bs
                        then
                          (let uu____4734 = FStar_Util.first_N n bs  in
                           match uu____4734 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____4812 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____4812
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____4829 =
                               FStar_Ident.string_of_lid fv_lid  in
                             let uu____4831 = FStar_Util.string_of_int n  in
                             let uu____4833 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____4829 uu____4831 uu____4833
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____4641 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____4884 =
                       let uu____4905 =
                         FStar_Util.prefix_until
                           (fun uu____4947  ->
                              match uu____4947 with
                              | (b,uu____4956) ->
                                  let uu____4961 =
                                    let uu____4962 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____4962.FStar_Syntax_Syntax.n  in
                                  (match uu____4961 with
                                   | FStar_Syntax_Syntax.Tm_type uu____4966
                                       -> false
                                   | uu____4968 -> true)) bs1
                          in
                       match uu____4905 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____4884 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____5210 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____5210) type_vars
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
                                let uu____5310 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____5310
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____5327 =
                                      let uu____5330 =
                                        let uu____5333 =
                                          lid_to_top_name fv_lid1  in
                                        let uu____5334 =
                                          let uu____5337 =
                                            let uu____5338 =
                                              let uu____5339 =
                                                let uu____5340 =
                                                  let uu____5352 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____5352,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____5340
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____5339
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____5338
                                             in
                                          [uu____5337; fv_lid_embedded; cb]
                                           in
                                        uu____5333 :: uu____5334  in
                                      res_embedding :: uu____5330  in
                                    FStar_List.append arg_unembeddings
                                      uu____5327
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
                                  let uu____5371 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____5371, arity, true)
                                else
                                  (let uu____5381 =
                                     let uu____5383 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____5383
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____5381
                                   then
                                     let h =
                                       let uu____5394 =
                                         let uu____5396 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____5396
                                          in
                                       str_to_top_name uu____5394  in
                                     let tac_fun =
                                       let uu____5399 =
                                         let uu____5400 =
                                           let uu____5407 =
                                             let uu____5408 =
                                               let uu____5410 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____5410
                                                in
                                             str_to_top_name uu____5408  in
                                           let uu____5412 =
                                             let uu____5415 =
                                               lid_to_top_name fv_lid1  in
                                             [uu____5415]  in
                                           (uu____5407, uu____5412)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____5400
                                          in
                                       FStar_All.pipe_left w uu____5399  in
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
                                           let uu____5429 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____5429
                                       | uu____5433 ->
                                           let uu____5437 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____5437
                                        in
                                     let uu____5440 =
                                       let uu____5441 = mk_lam "ncb" tabs  in
                                       mk_lam "psc" uu____5441  in
                                     (uu____5440, (arity + Prims.int_one),
                                       false)
                                   else
                                     (let uu____5450 =
                                        let uu____5451 =
                                          let uu____5453 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____5453
                                           in
                                        NoTacticEmbedding uu____5451  in
                                      FStar_Exn.raise uu____5450))
                            | (b,uu____5465)::bs4 ->
                                let uu____5485 =
                                  let uu____5488 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____5488 :: accum_embeddings  in
                                aux loc uu____5485 bs4
                             in
                          (try
                             (fun uu___688_5510  ->
                                match () with
                                | () ->
                                    let uu____5523 = aux Syntax_term [] bs2
                                       in
                                    (match uu____5523 with
                                     | (w1,a,b) ->
                                         let uu____5551 = aux NBE_t [] bs2
                                            in
                                         (match uu____5551 with
                                          | (w',uu____5573,uu____5574) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____5610 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____5610 msg);
                                FStar_Pervasives_Native.None))))
  