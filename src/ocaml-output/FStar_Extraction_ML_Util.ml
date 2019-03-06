open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____67910  ->
    let uu____67911 = FStar_Options.codegen ()  in
    uu____67911 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____67980 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____68010) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____68016) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____68021 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____68025 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_68039  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_68042 ->
          let uu____68043 =
            let uu____68045 = FStar_Range.string_of_range p  in
            let uu____68047 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____68045 uu____68047
             in
          failwith uu____68043
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____68064 =
        let uu____68065 =
          let uu____68066 =
            let uu____68078 = FStar_Util.string_of_int i  in
            (uu____68078, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____68066  in
        FStar_All.pipe_right uu____68065
          (fun _68091  -> FStar_Extraction_ML_Syntax.MLE_Const _68091)
         in
      FStar_All.pipe_right uu____68064
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____68100 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _68101  -> FStar_Extraction_ML_Syntax.MLE_Const _68101)
         in
      FStar_All.pipe_right uu____68100
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____68102 =
      let uu____68109 =
        let uu____68112 =
          let uu____68113 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____68113 cstr  in
        let uu____68116 =
          let uu____68119 =
            let uu____68120 =
              let uu____68122 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____68122 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____68120 cint  in
          let uu____68125 =
            let uu____68128 =
              let uu____68129 =
                let uu____68131 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____68131 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____68129 cint  in
            let uu____68134 =
              let uu____68137 =
                let uu____68138 =
                  let uu____68140 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____68140 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____68138 cint  in
              let uu____68143 =
                let uu____68146 =
                  let uu____68147 =
                    let uu____68149 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____68149 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____68147 cint  in
                [uu____68146]  in
              uu____68137 :: uu____68143  in
            uu____68128 :: uu____68134  in
          uu____68119 :: uu____68125  in
        uu____68112 :: uu____68116  in
      (mk_range_mle, uu____68109)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____68102
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____68166 ->
          let uu____68167 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____68167
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____68195 =
            FStar_Util.find_opt
              (fun uu____68211  ->
                 match uu____68211 with | (y,uu____68219) -> y = x) subst1
             in
          (match uu____68195 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____68243 =
            let uu____68250 = subst_aux subst1 t1  in
            let uu____68251 = subst_aux subst1 t2  in
            (uu____68250, f, uu____68251)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____68243
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____68258 =
            let uu____68265 = FStar_List.map (subst_aux subst1) args  in
            (uu____68265, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____68258
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____68273 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____68273
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____68289  ->
    fun args  ->
      match uu____68289 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____68303 =
               let uu____68304 = FStar_List.zip formals args  in
               subst_aux uu____68304 t  in
             FStar_Pervasives_Native.Some uu____68303)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____68336 = try_subst ts args  in
      match uu____68336 with
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
    fun uu___617_68353  ->
      match uu___617_68353 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____68362 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____68362 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____68368 = try_subst ts args  in
               (match uu____68368 with
                | FStar_Pervasives_Native.None  ->
                    let uu____68373 =
                      let uu____68375 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____68377 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____68379 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____68375 uu____68377 uu____68379
                       in
                    failwith uu____68373
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____68386 -> FStar_Pervasives_Native.None)
      | uu____68389 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____68403) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____68407 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_68419  ->
    match uu___618_68419 with
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
        | uu____68440 ->
            let uu____68445 =
              let uu____68447 = FStar_Range.string_of_range r  in
              let uu____68449 = eff_to_string f  in
              let uu____68451 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____68447
                uu____68449 uu____68451
               in
            failwith uu____68445
  
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
    (fun uu____68494  ->
       fun t  ->
         match uu____68494 with
         | (uu____68501,t0) ->
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
                | uu____68629 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____68666 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____68674 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____68674 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____68685;
                     FStar_Extraction_ML_Syntax.loc = uu____68686;_}
                   ->
                   let uu____68711 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____68711
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____68732 = type_leq unfold_ty t2 t2'  in
                        (if uu____68732
                         then
                           let body1 =
                             let uu____68746 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____68746
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____68754 =
                             let uu____68757 =
                               let uu____68758 =
                                 let uu____68763 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____68763
                                  in
                               FStar_All.pipe_left uu____68758
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____68757  in
                           (true, uu____68754)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____68803 =
                           let uu____68811 =
                             let uu____68814 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _68817  ->
                                  FStar_Pervasives_Native.Some _68817)
                               uu____68814
                              in
                           type_leq_c unfold_ty uu____68811 t2 t2'  in
                         match uu____68803 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____68842 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____68842
                               | uu____68853 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____68865 ->
                   let uu____68868 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____68868
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____68914 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____68914
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____68939 = unfold_ty t  in
                 match uu____68939 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____68954 = unfold_ty t'  in
                     (match uu____68954 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____68979 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____68979
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____69006,uu____69007)
              ->
              let uu____69014 = unfold_ty t  in
              (match uu____69014 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____69029 -> (false, FStar_Pervasives_Native.None))
          | (uu____69036,FStar_Extraction_ML_Syntax.MLTY_Named uu____69037)
              ->
              let uu____69044 = unfold_ty t'  in
              (match uu____69044 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____69059 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____69070 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____69085 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____69085 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____69116 =
          let uu____69123 = erase_effect_annotations t1  in
          let uu____69124 = erase_effect_annotations t2  in
          (uu____69123, FStar_Extraction_ML_Syntax.E_PURE, uu____69124)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____69116
    | uu____69125 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_69153  ->
    match uu___619_69153 with
    | (FStar_Util.Inl uu____69165,uu____69166)::uu____69167 -> true
    | uu____69191 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____69219  ->
    match uu____69219 with
    | (ns,n1) ->
        let uu____69241 =
          let uu____69243 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____69243  in
        if uu____69241
        then
          let uu____69253 =
            let uu____69255 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____69255  in
          FStar_Pervasives_Native.Some uu____69253
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____69274 = is_xtuple mlp  in
        (match uu____69274 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____69281 -> e)
    | uu____69285 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_69296  ->
    match uu___620_69296 with
    | f::uu____69303 ->
        let uu____69306 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____69306 with
         | (ns,uu____69317) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____69330 -> failwith "impos"
  
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
  fun uu____69396  ->
    match uu____69396 with
    | (ns,n1) ->
        let uu____69418 =
          let uu____69420 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____69420  in
        if uu____69418
        then
          let uu____69430 =
            let uu____69432 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____69432  in
          FStar_Pervasives_Native.Some uu____69430
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____69451 = is_xtuple_ty mlp  in
        (match uu____69451 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____69458 -> t)
    | uu____69462 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____69476 = codegen_fsharp ()  in
    if uu____69476
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____69498  ->
    match uu____69498 with
    | (ns,n1) ->
        let uu____69518 = codegen_fsharp ()  in
        if uu____69518
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____69546 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____69546, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____69580 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____69580
      then true
      else
        (let uu____69587 = unfold_ty t  in
         match uu____69587 with
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
            let uu____69617 =
              let uu____69624 = eraseTypeDeep unfold_ty tyd  in
              let uu____69628 = eraseTypeDeep unfold_ty tycd  in
              (uu____69624, etag, uu____69628)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____69617
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____69640 = erasableType unfold_ty t  in
          if uu____69640
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____69648 =
               let uu____69655 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____69655, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____69648)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____69666 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____69666
      | uu____69672 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____69683 =
    let uu____69688 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____69688  in
  FStar_All.pipe_left uu____69683
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
          let uu____69776 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____69776
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____69792 = FStar_Range.file_of_range r  in (line, uu____69792)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69815,b) ->
        let uu____69817 = doms_and_cod b  in
        (match uu____69817 with | (ds,c) -> ((a :: ds), c))
    | uu____69838 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____69851 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____69851
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69879,b) ->
        let uu____69881 = uncurry_mlty_fun b  in
        (match uu____69881 with | (args,res) -> ((a :: args), res))
    | uu____69902 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____69918 -> true
    | uu____69921 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____69932 -> uu____69932
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____69954 =
          let uu____69960 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____69960)  in
        FStar_Errors.log_issue r uu____69954
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____69973 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____69984 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____69995 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____70006 -> false
  
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
              let uu____70077 =
                let uu____70078 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____70078  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70077
               in
            let lid_to_top_name l =
              let uu____70085 =
                let uu____70086 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____70086  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70085
               in
            let str_to_name s =
              let uu____70095 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____70095  in
            let str_to_top_name s =
              let uu____70104 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____70104  in
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
              let uu____70142 =
                let uu____70143 =
                  let uu____70150 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____70152 =
                    let uu____70155 =
                      let uu____70156 =
                        let uu____70157 =
                          let uu____70158 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____70158
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____70157  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____70156
                       in
                    [uu____70155]  in
                  (uu____70150, uu____70152)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70143  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70142
               in
            let emb_prefix uu___621_70173 =
              match uu___621_70173 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____70187 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____70198 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____70227 =
                let uu____70229 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____70229  in
              emb_prefix l uu____70227  in
            let mk_any_embedding l s =
              let uu____70245 =
                let uu____70246 =
                  let uu____70253 = emb_prefix l "mk_any_emb"  in
                  let uu____70255 =
                    let uu____70258 = str_to_name s  in [uu____70258]  in
                  (uu____70253, uu____70255)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70246  in
              FStar_All.pipe_left w uu____70245  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____70308 =
                let uu____70309 =
                  let uu____70316 = emb_prefix l "e_arrow"  in
                  (uu____70316, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70309  in
              FStar_All.pipe_left w uu____70308  in
            let known_type_constructors =
              let term_cs =
                let uu____70354 =
                  let uu____70369 =
                    let uu____70384 =
                      let uu____70399 =
                        let uu____70414 =
                          let uu____70429 =
                            let uu____70444 =
                              let uu____70459 =
                                let uu____70472 =
                                  let uu____70481 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____70481, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____70472, Syntax_term)  in
                              let uu____70495 =
                                let uu____70510 =
                                  let uu____70523 =
                                    let uu____70532 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____70532, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____70523, Refl_emb)  in
                                let uu____70546 =
                                  let uu____70561 =
                                    let uu____70574 =
                                      let uu____70583 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____70583, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____70574, Refl_emb)  in
                                  let uu____70597 =
                                    let uu____70612 =
                                      let uu____70625 =
                                        let uu____70634 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____70634, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____70625, Refl_emb)  in
                                    let uu____70648 =
                                      let uu____70663 =
                                        let uu____70676 =
                                          let uu____70685 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____70685,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____70676, Refl_emb)  in
                                      let uu____70699 =
                                        let uu____70714 =
                                          let uu____70727 =
                                            let uu____70736 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____70736,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____70727, Refl_emb)  in
                                        [uu____70714]  in
                                      uu____70663 :: uu____70699  in
                                    uu____70612 :: uu____70648  in
                                  uu____70561 :: uu____70597  in
                                uu____70510 :: uu____70546  in
                              uu____70459 :: uu____70495  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____70444
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____70429
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____70414
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____70399
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____70384
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____70369
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____70354
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_71043  ->
                     match uu___622_71043 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____71118 -> failwith "Impossible") term_cs
                 in
              fun uu___623_71144  ->
                match uu___623_71144 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____71159 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____71196  ->
                   match uu____71196 with
                   | ((x,args,uu____71212),uu____71213) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____71243 =
              match uu____71243 with
              | (bv',uu____71251) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____71285 =
                let uu____71286 = FStar_Syntax_Subst.compress t3  in
                uu____71286.FStar_Syntax_Syntax.n  in
              match uu____71285 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____71295 =
                    let uu____71297 =
                      let uu____71303 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____71303  in
                    FStar_Pervasives_Native.snd uu____71297  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____71295
              | FStar_Syntax_Syntax.Tm_refine (x,uu____71324) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____71330,uu____71331)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____71404 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____71404 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____71426 =
                           let uu____71427 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____71427  in
                         uu____71426.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____71445 = mk_embedding l env t0  in
                       let uu____71446 = mk_embedding l env t11  in
                       emb_arrow l uu____71445 uu____71446)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____71517 =
                      let uu____71524 =
                        let uu____71525 =
                          let uu____71540 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____71540)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____71525  in
                      FStar_Syntax_Syntax.mk uu____71524  in
                    uu____71517 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____71568 ->
                  let uu____71569 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71569 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71621 =
                         let uu____71622 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71622.FStar_Syntax_Syntax.n  in
                       (match uu____71621 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71652  ->
                                      match uu____71652 with
                                      | (t4,uu____71660) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71667 =
                              let uu____71680 =
                                FStar_Util.find_opt
                                  (fun uu____71712  ->
                                     match uu____71712 with
                                     | ((x,uu____71727,uu____71728),uu____71729)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71680
                                FStar_Util.must
                               in
                            (match uu____71667 with
                             | ((uu____71780,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _71797 when
                                      _71797 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____71802 ->
                            let uu____71803 =
                              let uu____71804 =
                                let uu____71806 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____71806
                                 in
                              NoTacticEmbedding uu____71804  in
                            FStar_Exn.raise uu____71803))
              | FStar_Syntax_Syntax.Tm_uinst uu____71809 ->
                  let uu____71816 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71816 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71868 =
                         let uu____71869 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71869.FStar_Syntax_Syntax.n  in
                       (match uu____71868 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71899  ->
                                      match uu____71899 with
                                      | (t4,uu____71907) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71914 =
                              let uu____71927 =
                                FStar_Util.find_opt
                                  (fun uu____71959  ->
                                     match uu____71959 with
                                     | ((x,uu____71974,uu____71975),uu____71976)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71927
                                FStar_Util.must
                               in
                            (match uu____71914 with
                             | ((uu____72027,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72044 when
                                      _72044 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72049 ->
                            let uu____72050 =
                              let uu____72051 =
                                let uu____72053 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72053
                                 in
                              NoTacticEmbedding uu____72051  in
                            FStar_Exn.raise uu____72050))
              | FStar_Syntax_Syntax.Tm_app uu____72056 ->
                  let uu____72073 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____72073 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____72125 =
                         let uu____72126 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____72126.FStar_Syntax_Syntax.n  in
                       (match uu____72125 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____72156  ->
                                      match uu____72156 with
                                      | (t4,uu____72164) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____72171 =
                              let uu____72184 =
                                FStar_Util.find_opt
                                  (fun uu____72216  ->
                                     match uu____72216 with
                                     | ((x,uu____72231,uu____72232),uu____72233)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____72184
                                FStar_Util.must
                               in
                            (match uu____72171 with
                             | ((uu____72284,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72301 when
                                      _72301 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72306 ->
                            let uu____72307 =
                              let uu____72308 =
                                let uu____72310 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72310
                                 in
                              NoTacticEmbedding uu____72308  in
                            FStar_Exn.raise uu____72307))
              | uu____72313 ->
                  let uu____72314 =
                    let uu____72315 =
                      let uu____72317 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____72317
                       in
                    NoTacticEmbedding uu____72315  in
                  FStar_Exn.raise uu____72314
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____72339 =
                      let uu____72340 =
                        let uu____72347 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72349 =
                          let uu____72352 =
                            let uu____72353 =
                              let uu____72354 =
                                let uu____72355 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72355
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72354
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72353
                             in
                          let uu____72357 =
                            let uu____72360 =
                              let uu____72361 =
                                let uu____72362 =
                                  let uu____72363 =
                                    let uu____72370 =
                                      let uu____72373 = str_to_name "args"
                                         in
                                      [uu____72373]  in
                                    (body, uu____72370)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____72363
                                   in
                                FStar_All.pipe_left w uu____72362  in
                              mk_lam "_" uu____72361  in
                            [uu____72360]  in
                          uu____72352 :: uu____72357  in
                        (uu____72347, uu____72349)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72340  in
                    FStar_All.pipe_left w uu____72339  in
                  mk_lam "args" body1
              | uu____72381 ->
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
                    let uu____72430 =
                      let uu____72431 =
                        let uu____72432 =
                          let uu____72439 =
                            let uu____72442 = str_to_name "args"  in
                            [uu____72442]  in
                          (body, uu____72439)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72432  in
                      FStar_All.pipe_left w uu____72431  in
                    (pattern, FStar_Pervasives_Native.None, uu____72430)  in
                  let default_branch =
                    let uu____72457 =
                      let uu____72458 =
                        let uu____72459 =
                          let uu____72466 = str_to_name "failwith"  in
                          let uu____72468 =
                            let uu____72471 =
                              let uu____72472 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____72472  in
                            [uu____72471]  in
                          (uu____72466, uu____72468)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72459  in
                      FStar_All.pipe_left w uu____72458  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____72457)
                     in
                  let body1 =
                    let uu____72480 =
                      let uu____72481 =
                        let uu____72496 = str_to_name "args"  in
                        (uu____72496, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____72481  in
                    FStar_All.pipe_left w uu____72480  in
                  let body2 =
                    let uu____72533 =
                      let uu____72534 =
                        let uu____72541 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72543 =
                          let uu____72546 =
                            let uu____72547 =
                              let uu____72548 =
                                let uu____72549 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72549
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72548
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72547
                             in
                          let uu____72551 =
                            let uu____72554 = mk_lam "_" body1  in
                            [uu____72554]  in
                          uu____72546 :: uu____72551  in
                        (uu____72541, uu____72543)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72534  in
                    FStar_All.pipe_left w uu____72533  in
                  mk_lam "args" body2
               in
            let uu____72559 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____72559 with
            | (bs,c) ->
                let uu____72592 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____72693 = FStar_Util.first_N n1 bs  in
                           match uu____72693 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____72771 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____72771
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____72788 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____72790 = FStar_Util.string_of_int n1
                                in
                             let uu____72792 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____72788 uu____72790 uu____72792
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____72592 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____72849 =
                       let uu____72870 =
                         FStar_Util.prefix_until
                           (fun uu____72912  ->
                              match uu____72912 with
                              | (b,uu____72921) ->
                                  let uu____72926 =
                                    let uu____72927 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____72927.FStar_Syntax_Syntax.n  in
                                  (match uu____72926 with
                                   | FStar_Syntax_Syntax.Tm_type uu____72931
                                       -> false
                                   | uu____72933 -> true)) bs1
                          in
                       match uu____72870 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____72849 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____73175 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____73175) type_vars
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
                                let uu____73275 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____73275
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____73296 =
                                      let uu____73299 =
                                        let uu____73302 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____73303 =
                                          let uu____73306 =
                                            let uu____73307 =
                                              let uu____73308 =
                                                let uu____73309 =
                                                  let uu____73321 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____73321,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____73309
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____73308
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____73307
                                             in
                                          [uu____73306; fv_lid_embedded; cb]
                                           in
                                        uu____73302 :: uu____73303  in
                                      res_embedding :: uu____73299  in
                                    FStar_List.append arg_unembeddings
                                      uu____73296
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
                                  let uu____73346 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____73346, arity, true)
                                else
                                  (let uu____73360 =
                                     let uu____73362 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____73362
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____73360
                                   then
                                     let h =
                                       let uu____73373 =
                                         let uu____73375 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____73375
                                          in
                                       str_to_top_name uu____73373  in
                                     let tac_fun =
                                       let uu____73384 =
                                         let uu____73385 =
                                           let uu____73392 =
                                             let uu____73393 =
                                               let uu____73395 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____73395
                                                in
                                             str_to_top_name uu____73393  in
                                           let uu____73403 =
                                             let uu____73406 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____73406]  in
                                           (uu____73392, uu____73403)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____73385
                                          in
                                       FStar_All.pipe_left w uu____73384  in
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
                                           let uu____73420 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____73420
                                       | uu____73424 ->
                                           let uu____73428 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____73428
                                        in
                                     let uu____73431 =
                                       let uu____73432 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____73432  in
                                     (uu____73431,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____73447 =
                                        let uu____73448 =
                                          let uu____73450 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____73450
                                           in
                                        NoTacticEmbedding uu____73448  in
                                      FStar_Exn.raise uu____73447))
                            | (b,uu____73462)::bs4 ->
                                let uu____73482 =
                                  let uu____73485 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____73485 :: accum_embeddings  in
                                aux loc uu____73482 bs4
                             in
                          (try
                             (fun uu___1304_73507  ->
                                match () with
                                | () ->
                                    let uu____73520 = aux Syntax_term [] bs2
                                       in
                                    (match uu____73520 with
                                     | (w1,a,b) ->
                                         let uu____73548 = aux NBE_t [] bs2
                                            in
                                         (match uu____73548 with
                                          | (w',uu____73570,uu____73571) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____73607 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____73607 msg);
                                FStar_Pervasives_Native.None))))
  