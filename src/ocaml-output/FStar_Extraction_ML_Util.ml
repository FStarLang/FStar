open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____67887  ->
    let uu____67888 = FStar_Options.codegen ()  in
    uu____67888 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____67957 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____67987) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____67993) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____67998 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____68002 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_68016  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_68019 ->
          let uu____68020 =
            let uu____68022 = FStar_Range.string_of_range p  in
            let uu____68024 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____68022 uu____68024
             in
          failwith uu____68020
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____68041 =
        let uu____68042 =
          let uu____68043 =
            let uu____68055 = FStar_Util.string_of_int i  in
            (uu____68055, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____68043  in
        FStar_All.pipe_right uu____68042
          (fun _68068  -> FStar_Extraction_ML_Syntax.MLE_Const _68068)
         in
      FStar_All.pipe_right uu____68041
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____68077 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _68078  -> FStar_Extraction_ML_Syntax.MLE_Const _68078)
         in
      FStar_All.pipe_right uu____68077
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____68079 =
      let uu____68086 =
        let uu____68089 =
          let uu____68090 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____68090 cstr  in
        let uu____68093 =
          let uu____68096 =
            let uu____68097 =
              let uu____68099 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____68099 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____68097 cint  in
          let uu____68102 =
            let uu____68105 =
              let uu____68106 =
                let uu____68108 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____68108 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____68106 cint  in
            let uu____68111 =
              let uu____68114 =
                let uu____68115 =
                  let uu____68117 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____68117 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____68115 cint  in
              let uu____68120 =
                let uu____68123 =
                  let uu____68124 =
                    let uu____68126 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____68126 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____68124 cint  in
                [uu____68123]  in
              uu____68114 :: uu____68120  in
            uu____68105 :: uu____68111  in
          uu____68096 :: uu____68102  in
        uu____68089 :: uu____68093  in
      (mk_range_mle, uu____68086)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____68079
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____68143 ->
          let uu____68144 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____68144
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____68172 =
            FStar_Util.find_opt
              (fun uu____68188  ->
                 match uu____68188 with | (y,uu____68196) -> y = x) subst1
             in
          (match uu____68172 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____68220 =
            let uu____68227 = subst_aux subst1 t1  in
            let uu____68228 = subst_aux subst1 t2  in
            (uu____68227, f, uu____68228)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____68220
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____68235 =
            let uu____68242 = FStar_List.map (subst_aux subst1) args  in
            (uu____68242, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____68235
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____68250 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____68250
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____68266  ->
    fun args  ->
      match uu____68266 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____68280 =
               let uu____68281 = FStar_List.zip formals args  in
               subst_aux uu____68281 t  in
             FStar_Pervasives_Native.Some uu____68280)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____68313 = try_subst ts args  in
      match uu____68313 with
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
    fun uu___617_68330  ->
      match uu___617_68330 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____68339 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____68339 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____68345 = try_subst ts args  in
               (match uu____68345 with
                | FStar_Pervasives_Native.None  ->
                    let uu____68350 =
                      let uu____68352 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____68354 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____68356 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____68352 uu____68354 uu____68356
                       in
                    failwith uu____68350
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____68363 -> FStar_Pervasives_Native.None)
      | uu____68366 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____68380) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____68384 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_68396  ->
    match uu___618_68396 with
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
        | uu____68417 ->
            let uu____68422 =
              let uu____68424 = FStar_Range.string_of_range r  in
              let uu____68426 = eff_to_string f  in
              let uu____68428 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____68424
                uu____68426 uu____68428
               in
            failwith uu____68422
  
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
    (fun uu____68471  ->
       fun t  ->
         match uu____68471 with
         | (uu____68478,t0) ->
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
                | uu____68606 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____68643 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____68651 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____68651 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____68662;
                     FStar_Extraction_ML_Syntax.loc = uu____68663;_}
                   ->
                   let uu____68688 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____68688
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____68709 = type_leq unfold_ty t2 t2'  in
                        (if uu____68709
                         then
                           let body1 =
                             let uu____68723 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____68723
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____68731 =
                             let uu____68734 =
                               let uu____68735 =
                                 let uu____68740 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____68740
                                  in
                               FStar_All.pipe_left uu____68735
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____68734  in
                           (true, uu____68731)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____68780 =
                           let uu____68788 =
                             let uu____68791 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _68794  ->
                                  FStar_Pervasives_Native.Some _68794)
                               uu____68791
                              in
                           type_leq_c unfold_ty uu____68788 t2 t2'  in
                         match uu____68780 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____68819 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____68819
                               | uu____68830 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____68842 ->
                   let uu____68845 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____68845
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____68891 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____68891
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____68916 = unfold_ty t  in
                 match uu____68916 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____68931 = unfold_ty t'  in
                     (match uu____68931 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____68956 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____68956
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____68983,uu____68984)
              ->
              let uu____68991 = unfold_ty t  in
              (match uu____68991 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____69006 -> (false, FStar_Pervasives_Native.None))
          | (uu____69013,FStar_Extraction_ML_Syntax.MLTY_Named uu____69014)
              ->
              let uu____69021 = unfold_ty t'  in
              (match uu____69021 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____69036 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____69047 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____69062 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____69062 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____69093 =
          let uu____69100 = erase_effect_annotations t1  in
          let uu____69101 = erase_effect_annotations t2  in
          (uu____69100, FStar_Extraction_ML_Syntax.E_PURE, uu____69101)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____69093
    | uu____69102 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_69130  ->
    match uu___619_69130 with
    | (FStar_Util.Inl uu____69142,uu____69143)::uu____69144 -> true
    | uu____69168 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____69196  ->
    match uu____69196 with
    | (ns,n1) ->
        let uu____69218 =
          let uu____69220 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____69220  in
        if uu____69218
        then
          let uu____69230 =
            let uu____69232 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____69232  in
          FStar_Pervasives_Native.Some uu____69230
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____69251 = is_xtuple mlp  in
        (match uu____69251 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____69258 -> e)
    | uu____69262 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_69273  ->
    match uu___620_69273 with
    | f::uu____69280 ->
        let uu____69283 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____69283 with
         | (ns,uu____69294) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____69307 -> failwith "impos"
  
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
  fun uu____69373  ->
    match uu____69373 with
    | (ns,n1) ->
        let uu____69395 =
          let uu____69397 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____69397  in
        if uu____69395
        then
          let uu____69407 =
            let uu____69409 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____69409  in
          FStar_Pervasives_Native.Some uu____69407
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____69428 = is_xtuple_ty mlp  in
        (match uu____69428 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____69435 -> t)
    | uu____69439 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____69453 = codegen_fsharp ()  in
    if uu____69453
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____69475  ->
    match uu____69475 with
    | (ns,n1) ->
        let uu____69495 = codegen_fsharp ()  in
        if uu____69495
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____69523 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____69523, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____69557 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____69557
      then true
      else
        (let uu____69564 = unfold_ty t  in
         match uu____69564 with
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
            let uu____69594 =
              let uu____69601 = eraseTypeDeep unfold_ty tyd  in
              let uu____69605 = eraseTypeDeep unfold_ty tycd  in
              (uu____69601, etag, uu____69605)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____69594
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____69617 = erasableType unfold_ty t  in
          if uu____69617
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____69625 =
               let uu____69632 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____69632, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____69625)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____69643 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____69643
      | uu____69649 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____69660 =
    let uu____69665 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____69665  in
  FStar_All.pipe_left uu____69660
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
          let uu____69753 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____69753
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____69769 = FStar_Range.file_of_range r  in (line, uu____69769)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69792,b) ->
        let uu____69794 = doms_and_cod b  in
        (match uu____69794 with | (ds,c) -> ((a :: ds), c))
    | uu____69815 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____69828 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____69828
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69856,b) ->
        let uu____69858 = uncurry_mlty_fun b  in
        (match uu____69858 with | (args,res) -> ((a :: args), res))
    | uu____69879 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____69895 -> true
    | uu____69898 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____69909 -> uu____69909
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____69931 =
          let uu____69937 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____69937)  in
        FStar_Errors.log_issue r uu____69931
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____69950 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____69961 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____69972 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____69983 -> false
  
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
              let uu____70054 =
                let uu____70055 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____70055  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70054
               in
            let lid_to_top_name l =
              let uu____70062 =
                let uu____70063 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____70063  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70062
               in
            let str_to_name s =
              let uu____70072 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____70072  in
            let str_to_top_name s =
              let uu____70081 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____70081  in
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
              let uu____70119 =
                let uu____70120 =
                  let uu____70127 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____70129 =
                    let uu____70132 =
                      let uu____70133 =
                        let uu____70134 =
                          let uu____70135 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____70135
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____70134  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____70133
                       in
                    [uu____70132]  in
                  (uu____70127, uu____70129)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70120  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70119
               in
            let emb_prefix uu___621_70150 =
              match uu___621_70150 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____70164 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____70175 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____70204 =
                let uu____70206 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____70206  in
              emb_prefix l uu____70204  in
            let mk_any_embedding l s =
              let uu____70222 =
                let uu____70223 =
                  let uu____70230 = emb_prefix l "mk_any_emb"  in
                  let uu____70232 =
                    let uu____70235 = str_to_name s  in [uu____70235]  in
                  (uu____70230, uu____70232)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70223  in
              FStar_All.pipe_left w uu____70222  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____70285 =
                let uu____70286 =
                  let uu____70293 = emb_prefix l "e_arrow"  in
                  (uu____70293, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70286  in
              FStar_All.pipe_left w uu____70285  in
            let known_type_constructors =
              let term_cs =
                let uu____70331 =
                  let uu____70346 =
                    let uu____70361 =
                      let uu____70376 =
                        let uu____70391 =
                          let uu____70406 =
                            let uu____70421 =
                              let uu____70436 =
                                let uu____70449 =
                                  let uu____70458 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____70458, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____70449, Syntax_term)  in
                              let uu____70472 =
                                let uu____70487 =
                                  let uu____70500 =
                                    let uu____70509 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____70509, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____70500, Refl_emb)  in
                                let uu____70523 =
                                  let uu____70538 =
                                    let uu____70551 =
                                      let uu____70560 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____70560, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____70551, Refl_emb)  in
                                  let uu____70574 =
                                    let uu____70589 =
                                      let uu____70602 =
                                        let uu____70611 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____70611, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____70602, Refl_emb)  in
                                    let uu____70625 =
                                      let uu____70640 =
                                        let uu____70653 =
                                          let uu____70662 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____70662,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____70653, Refl_emb)  in
                                      let uu____70676 =
                                        let uu____70691 =
                                          let uu____70704 =
                                            let uu____70713 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____70713,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____70704, Refl_emb)  in
                                        [uu____70691]  in
                                      uu____70640 :: uu____70676  in
                                    uu____70589 :: uu____70625  in
                                  uu____70538 :: uu____70574  in
                                uu____70487 :: uu____70523  in
                              uu____70436 :: uu____70472  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____70421
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____70406
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____70391
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____70376
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____70361
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____70346
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____70331
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_71020  ->
                     match uu___622_71020 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____71095 -> failwith "Impossible") term_cs
                 in
              fun uu___623_71121  ->
                match uu___623_71121 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____71136 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____71173  ->
                   match uu____71173 with
                   | ((x,args,uu____71189),uu____71190) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____71220 =
              match uu____71220 with
              | (bv',uu____71228) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____71262 =
                let uu____71263 = FStar_Syntax_Subst.compress t3  in
                uu____71263.FStar_Syntax_Syntax.n  in
              match uu____71262 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____71272 =
                    let uu____71274 =
                      let uu____71280 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____71280  in
                    FStar_Pervasives_Native.snd uu____71274  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____71272
              | FStar_Syntax_Syntax.Tm_refine (x,uu____71301) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____71307,uu____71308)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____71381 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____71381 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____71403 =
                           let uu____71404 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____71404  in
                         uu____71403.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____71422 = mk_embedding l env t0  in
                       let uu____71423 = mk_embedding l env t11  in
                       emb_arrow l uu____71422 uu____71423)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____71494 =
                      let uu____71501 =
                        let uu____71502 =
                          let uu____71517 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____71517)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____71502  in
                      FStar_Syntax_Syntax.mk uu____71501  in
                    uu____71494 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____71545 ->
                  let uu____71546 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71546 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71598 =
                         let uu____71599 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71599.FStar_Syntax_Syntax.n  in
                       (match uu____71598 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71629  ->
                                      match uu____71629 with
                                      | (t4,uu____71637) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71644 =
                              let uu____71657 =
                                FStar_Util.find_opt
                                  (fun uu____71689  ->
                                     match uu____71689 with
                                     | ((x,uu____71704,uu____71705),uu____71706)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71657
                                FStar_Util.must
                               in
                            (match uu____71644 with
                             | ((uu____71757,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _71774 when
                                      _71774 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____71779 ->
                            let uu____71780 =
                              let uu____71781 =
                                let uu____71783 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____71783
                                 in
                              NoTacticEmbedding uu____71781  in
                            FStar_Exn.raise uu____71780))
              | FStar_Syntax_Syntax.Tm_uinst uu____71786 ->
                  let uu____71793 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71793 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71845 =
                         let uu____71846 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71846.FStar_Syntax_Syntax.n  in
                       (match uu____71845 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71876  ->
                                      match uu____71876 with
                                      | (t4,uu____71884) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71891 =
                              let uu____71904 =
                                FStar_Util.find_opt
                                  (fun uu____71936  ->
                                     match uu____71936 with
                                     | ((x,uu____71951,uu____71952),uu____71953)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71904
                                FStar_Util.must
                               in
                            (match uu____71891 with
                             | ((uu____72004,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72021 when
                                      _72021 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72026 ->
                            let uu____72027 =
                              let uu____72028 =
                                let uu____72030 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72030
                                 in
                              NoTacticEmbedding uu____72028  in
                            FStar_Exn.raise uu____72027))
              | FStar_Syntax_Syntax.Tm_app uu____72033 ->
                  let uu____72050 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____72050 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____72102 =
                         let uu____72103 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____72103.FStar_Syntax_Syntax.n  in
                       (match uu____72102 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____72133  ->
                                      match uu____72133 with
                                      | (t4,uu____72141) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____72148 =
                              let uu____72161 =
                                FStar_Util.find_opt
                                  (fun uu____72193  ->
                                     match uu____72193 with
                                     | ((x,uu____72208,uu____72209),uu____72210)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____72161
                                FStar_Util.must
                               in
                            (match uu____72148 with
                             | ((uu____72261,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72278 when
                                      _72278 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72283 ->
                            let uu____72284 =
                              let uu____72285 =
                                let uu____72287 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72287
                                 in
                              NoTacticEmbedding uu____72285  in
                            FStar_Exn.raise uu____72284))
              | uu____72290 ->
                  let uu____72291 =
                    let uu____72292 =
                      let uu____72294 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____72294
                       in
                    NoTacticEmbedding uu____72292  in
                  FStar_Exn.raise uu____72291
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____72316 =
                      let uu____72317 =
                        let uu____72324 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72326 =
                          let uu____72329 =
                            let uu____72330 =
                              let uu____72331 =
                                let uu____72332 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72332
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72331
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72330
                             in
                          let uu____72334 =
                            let uu____72337 =
                              let uu____72338 =
                                let uu____72339 =
                                  let uu____72340 =
                                    let uu____72347 =
                                      let uu____72350 = str_to_name "args"
                                         in
                                      [uu____72350]  in
                                    (body, uu____72347)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____72340
                                   in
                                FStar_All.pipe_left w uu____72339  in
                              mk_lam "_" uu____72338  in
                            [uu____72337]  in
                          uu____72329 :: uu____72334  in
                        (uu____72324, uu____72326)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72317  in
                    FStar_All.pipe_left w uu____72316  in
                  mk_lam "args" body1
              | uu____72358 ->
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
                    let uu____72407 =
                      let uu____72408 =
                        let uu____72409 =
                          let uu____72416 =
                            let uu____72419 = str_to_name "args"  in
                            [uu____72419]  in
                          (body, uu____72416)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72409  in
                      FStar_All.pipe_left w uu____72408  in
                    (pattern, FStar_Pervasives_Native.None, uu____72407)  in
                  let default_branch =
                    let uu____72434 =
                      let uu____72435 =
                        let uu____72436 =
                          let uu____72443 = str_to_name "failwith"  in
                          let uu____72445 =
                            let uu____72448 =
                              let uu____72449 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____72449  in
                            [uu____72448]  in
                          (uu____72443, uu____72445)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72436  in
                      FStar_All.pipe_left w uu____72435  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____72434)
                     in
                  let body1 =
                    let uu____72457 =
                      let uu____72458 =
                        let uu____72473 = str_to_name "args"  in
                        (uu____72473, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____72458  in
                    FStar_All.pipe_left w uu____72457  in
                  let body2 =
                    let uu____72510 =
                      let uu____72511 =
                        let uu____72518 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72520 =
                          let uu____72523 =
                            let uu____72524 =
                              let uu____72525 =
                                let uu____72526 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72526
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72525
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72524
                             in
                          let uu____72528 =
                            let uu____72531 = mk_lam "_" body1  in
                            [uu____72531]  in
                          uu____72523 :: uu____72528  in
                        (uu____72518, uu____72520)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72511  in
                    FStar_All.pipe_left w uu____72510  in
                  mk_lam "args" body2
               in
            let uu____72536 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____72536 with
            | (bs,c) ->
                let uu____72569 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____72670 = FStar_Util.first_N n1 bs  in
                           match uu____72670 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____72748 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____72748
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____72765 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____72767 = FStar_Util.string_of_int n1
                                in
                             let uu____72769 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____72765 uu____72767 uu____72769
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____72569 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____72826 =
                       let uu____72847 =
                         FStar_Util.prefix_until
                           (fun uu____72889  ->
                              match uu____72889 with
                              | (b,uu____72898) ->
                                  let uu____72903 =
                                    let uu____72904 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____72904.FStar_Syntax_Syntax.n  in
                                  (match uu____72903 with
                                   | FStar_Syntax_Syntax.Tm_type uu____72908
                                       -> false
                                   | uu____72910 -> true)) bs1
                          in
                       match uu____72847 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____72826 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____73152 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____73152) type_vars
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
                                let uu____73252 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____73252
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____73273 =
                                      let uu____73276 =
                                        let uu____73279 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____73280 =
                                          let uu____73283 =
                                            let uu____73284 =
                                              let uu____73285 =
                                                let uu____73286 =
                                                  let uu____73298 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____73298,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____73286
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____73285
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____73284
                                             in
                                          [uu____73283; fv_lid_embedded; cb]
                                           in
                                        uu____73279 :: uu____73280  in
                                      res_embedding :: uu____73276  in
                                    FStar_List.append arg_unembeddings
                                      uu____73273
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
                                  let uu____73323 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____73323, arity, true)
                                else
                                  (let uu____73337 =
                                     let uu____73339 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____73339
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____73337
                                   then
                                     let h =
                                       let uu____73350 =
                                         let uu____73352 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____73352
                                          in
                                       str_to_top_name uu____73350  in
                                     let tac_fun =
                                       let uu____73361 =
                                         let uu____73362 =
                                           let uu____73369 =
                                             let uu____73370 =
                                               let uu____73372 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____73372
                                                in
                                             str_to_top_name uu____73370  in
                                           let uu____73380 =
                                             let uu____73383 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____73383]  in
                                           (uu____73369, uu____73380)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____73362
                                          in
                                       FStar_All.pipe_left w uu____73361  in
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
                                           let uu____73397 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____73397
                                       | uu____73401 ->
                                           let uu____73405 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____73405
                                        in
                                     let uu____73408 =
                                       let uu____73409 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____73409  in
                                     (uu____73408,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____73424 =
                                        let uu____73425 =
                                          let uu____73427 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____73427
                                           in
                                        NoTacticEmbedding uu____73425  in
                                      FStar_Exn.raise uu____73424))
                            | (b,uu____73439)::bs4 ->
                                let uu____73459 =
                                  let uu____73462 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____73462 :: accum_embeddings  in
                                aux loc uu____73459 bs4
                             in
                          (try
                             (fun uu___1304_73484  ->
                                match () with
                                | () ->
                                    let uu____73497 = aux Syntax_term [] bs2
                                       in
                                    (match uu____73497 with
                                     | (w1,a,b) ->
                                         let uu____73525 = aux NBE_t [] bs2
                                            in
                                         (match uu____73525 with
                                          | (w',uu____73547,uu____73548) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____73584 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____73584 msg);
                                FStar_Pervasives_Native.None))))
  