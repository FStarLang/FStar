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
    | FStar_Const.Const_string (s,uu____90) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____91 ->
        failwith "Unhandled constant: reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try (fun uu___260_103  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___259_106 ->
          let uu____107 =
            let uu____108 = FStar_Range.string_of_range p  in
            let uu____109 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____108 uu____109
             in
          failwith uu____107
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____121 =
        let uu____122 =
          let uu____123 =
            let uu____134 = FStar_Util.string_of_int i  in
            (uu____134, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____123  in
        FStar_All.pipe_right uu____122
          (fun _0_17  -> FStar_Extraction_ML_Syntax.MLE_Const _0_17)
         in
      FStar_All.pipe_right uu____121
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____151 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_18  -> FStar_Extraction_ML_Syntax.MLE_Const _0_18)
         in
      FStar_All.pipe_right uu____151
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____152 =
      let uu____159 =
        let uu____162 =
          let uu____163 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____163 cstr  in
        let uu____164 =
          let uu____167 =
            let uu____168 =
              let uu____169 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____169 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____168 cint  in
          let uu____170 =
            let uu____173 =
              let uu____174 =
                let uu____175 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____175 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____174 cint  in
            let uu____176 =
              let uu____179 =
                let uu____180 =
                  let uu____181 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____181 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____180 cint  in
              let uu____182 =
                let uu____185 =
                  let uu____186 =
                    let uu____187 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____187 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____186 cint  in
                [uu____185]  in
              uu____179 :: uu____182  in
            uu____173 :: uu____176  in
          uu____167 :: uu____170  in
        uu____162 :: uu____164  in
      (mk_range_mle, uu____159)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____152
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____201 ->
          let uu____202 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____202
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____226 =
            FStar_Util.find_opt
              (fun uu____240  ->
                 match uu____240 with | (y,uu____246) -> y = x) subst1
             in
          (match uu____226 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____263 =
            let uu____270 = subst_aux subst1 t1  in
            let uu____271 = subst_aux subst1 t2  in (uu____270, f, uu____271)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____263
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____290 =
            let uu____297 = FStar_List.map (subst_aux subst1) args  in
            (uu____297, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____290
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____305 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____305
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____320  ->
    fun args  ->
      match uu____320 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____335 =
               let uu____336 = FStar_List.zip formals args  in
               subst_aux uu____336 t  in
             FStar_Pervasives_Native.Some uu____335)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____365 = try_subst ts args  in
      match uu____365 with
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
    fun uu___255_380  ->
      match uu___255_380 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____401 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____401 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____419 = try_subst ts args  in
               (match uu____419 with
                | FStar_Pervasives_Native.None  ->
                    let uu____424 =
                      let uu____425 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____426 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____427 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____425 uu____426 uu____427
                       in
                    failwith uu____424
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____433 -> FStar_Pervasives_Native.None)
      | uu____436 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____447) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____448 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___256_457  ->
    match uu___256_457 with
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
        | uu____473 ->
            let uu____478 =
              let uu____479 = FStar_Range.string_of_range r  in
              let uu____480 = eff_to_string f  in
              let uu____481 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____479
                uu____480 uu____481
               in
            failwith uu____478
  
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
    (fun uu____518  ->
       fun t  ->
         match uu____518 with
         | (uu____524,t0) ->
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
                | uu____633 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____665 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____672 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____672 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____682;
                     FStar_Extraction_ML_Syntax.loc = uu____683;_}
                   ->
                   let uu____704 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____704
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____720 = type_leq unfold_ty t2 t2'  in
                        (if uu____720
                         then
                           let body1 =
                             let uu____731 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____731
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____736 =
                             let uu____739 =
                               let uu____740 =
                                 let uu____745 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____745
                                  in
                               FStar_All.pipe_left uu____740
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____739  in
                           (true, uu____736)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____774 =
                           let uu____781 =
                             let uu____784 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_19  ->
                                  FStar_Pervasives_Native.Some _0_19)
                               uu____784
                              in
                           type_leq_c unfold_ty uu____781 t2 t2'  in
                         match uu____774 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____808 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____808
                               | uu____817 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____825 ->
                   let uu____828 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____828
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____894 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____894
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____910 = unfold_ty t  in
                 match uu____910 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____924 = unfold_ty t'  in
                     (match uu____924 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____946 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____946
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____963,uu____964) ->
              let uu____971 = unfold_ty t  in
              (match uu____971 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____985 -> (false, FStar_Pervasives_Native.None))
          | (uu____990,FStar_Extraction_ML_Syntax.MLTY_Named uu____991) ->
              let uu____998 = unfold_ty t'  in
              (match uu____998 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____1012 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____1019 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____1031 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____1031 FStar_Pervasives_Native.fst

let is_type_abstraction :
  'a 'b 'c .
    (('a,'b) FStar_Util.either,'c) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.bool
  =
  fun uu___257_1074  ->
    match uu___257_1074 with
    | (FStar_Util.Inl uu____1085,uu____1086)::uu____1087 -> true
    | uu____1110 -> false
  
let (is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1133  ->
    match uu____1133 with
    | (ns,n1) ->
        let uu____1148 =
          let uu____1149 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____1149  in
        if uu____1148
        then
          let uu____1152 =
            let uu____1153 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____1153  in
          FStar_Pervasives_Native.Some uu____1152
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1179 = is_xtuple mlp  in
        (match uu____1179 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1183 -> e)
    | uu____1186 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___258_1195  ->
    match uu___258_1195 with
    | f::uu____1201 ->
        let uu____1204 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1204 with
         | (ns,uu____1214) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1225 -> failwith "impos"
  
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
  fun uu____1281  ->
    match uu____1281 with
    | (ns,n1) ->
        let uu____1296 =
          let uu____1297 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1297  in
        if uu____1296
        then
          let uu____1300 =
            let uu____1301 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1301  in
          FStar_Pervasives_Native.Some uu____1300
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1327 = is_xtuple_ty mlp  in
        (match uu____1327 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1331 -> t)
    | uu____1334 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1344 = codegen_fsharp ()  in
    if uu____1344
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1356  ->
    match uu____1356 with
    | (ns,n1) ->
        let uu____1369 = codegen_fsharp ()  in
        if uu____1369
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____1382 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1382, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1408 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1408
      then true
      else
        (let uu____1410 = unfold_ty t  in
         match uu____1410 with
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
            let uu____1436 =
              let uu____1443 = eraseTypeDeep unfold_ty tyd  in
              let uu____1447 = eraseTypeDeep unfold_ty tycd  in
              (uu____1443, etag, uu____1447)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1436
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1470 = erasableType unfold_ty t  in
          if uu____1470
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1475 =
               let uu____1482 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1482, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1475)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1493 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1493
      | uu____1499 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1502 =
    let uu____1507 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1507  in
  FStar_All.pipe_left uu____1502
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
          let uu____1580 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1580
  
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1592 = FStar_Range.file_of_range r  in (line, uu____1592)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1611,b) ->
        let uu____1613 = doms_and_cod b  in
        (match uu____1613 with | (ds,c) -> ((a :: ds), c))
    | uu____1634 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1646 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1646
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1673,b) ->
        let uu____1675 = uncurry_mlty_fun b  in
        (match uu____1675 with | (args,res) -> ((a :: args), res))
    | uu____1696 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____1708 -> true
    | uu____1709 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____1716 -> uu____1716
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1732 =
          let uu____1737 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1737)  in
        FStar_Errors.log_issue r uu____1732
  
type emb_loc =
  | S 
  | R 
let (uu___is_S : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | S  -> true | uu____1743 -> false 
let (uu___is_R : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | R  -> true | uu____1749 -> false 
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
            let uu____1790 =
              let uu____1791 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1791  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1790
             in
          let lid_to_top_name l =
            let uu____1798 =
              let uu____1799 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1799  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1798
             in
          let str_to_name s =
            let uu____1806 = FStar_Ident.lid_of_str s  in
            lid_to_name uu____1806  in
          let str_to_top_name s =
            let uu____1813 = FStar_Ident.lid_of_str s  in
            lid_to_top_name uu____1813  in
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
            let uu____1851 =
              let uu____1852 = FStar_Util.string_of_int arity  in
              Prims.strcat "embed_arrow_" uu____1852  in
            fstar_syn_emb_prefix uu____1851  in
          let mk_any_embedding s =
            let uu____1859 =
              let uu____1860 =
                let uu____1867 = fstar_syn_emb_prefix "mk_any_emb"  in
                let uu____1868 =
                  let uu____1871 = str_to_name s  in [uu____1871]  in
                (uu____1867, uu____1868)  in
              FStar_Extraction_ML_Syntax.MLE_App uu____1860  in
            FStar_All.pipe_left w uu____1859  in
          let mk_lam nm e =
            FStar_All.pipe_left w
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
             in
          let known_type_constructors =
            let uu____1910 =
              let uu____1921 =
                let uu____1932 =
                  let uu____1943 =
                    let uu____1954 =
                      let uu____1963 =
                        FStar_Reflection_Data.fstar_refl_types_lid "term"  in
                      (uu____1963, (Prims.parse_int "0"), "term", R)  in
                    let uu____1964 =
                      let uu____1975 =
                        let uu____1984 =
                          FStar_Reflection_Data.fstar_refl_types_lid "fv"  in
                        (uu____1984, (Prims.parse_int "0"), "fv", R)  in
                      let uu____1985 =
                        let uu____1996 =
                          let uu____2005 =
                            FStar_Reflection_Data.fstar_refl_types_lid
                              "binder"
                             in
                          (uu____2005, (Prims.parse_int "0"), "binder", R)
                           in
                        let uu____2006 =
                          let uu____2017 =
                            let uu____2026 =
                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                "binders"
                               in
                            (uu____2026, (Prims.parse_int "0"), "binders", R)
                             in
                          let uu____2027 =
                            let uu____2038 =
                              let uu____2049 =
                                let uu____2060 =
                                  let uu____2071 =
                                    let uu____2080 =
                                      FStar_Parser_Const.mk_tuple_lid
                                        (Prims.parse_int "2")
                                        FStar_Range.dummyRange
                                       in
                                    (uu____2080, (Prims.parse_int "2"),
                                      "tuple2", S)
                                     in
                                  let uu____2081 =
                                    let uu____2092 =
                                      let uu____2101 =
                                        FStar_Reflection_Data.fstar_refl_data_lid
                                          "exp"
                                         in
                                      (uu____2101, (Prims.parse_int "0"),
                                        "exp", R)
                                       in
                                    [uu____2092]  in
                                  uu____2071 :: uu____2081  in
                                (FStar_Parser_Const.option_lid,
                                  (Prims.parse_int "1"), "option", S) ::
                                  uu____2060
                                 in
                              (FStar_Parser_Const.list_lid,
                                (Prims.parse_int "1"), "list", S) ::
                                uu____2049
                               in
                            (FStar_Parser_Const.norm_step_lid,
                              (Prims.parse_int "0"), "norm_step", S) ::
                              uu____2038
                             in
                          uu____2017 :: uu____2027  in
                        uu____1996 :: uu____2006  in
                      uu____1975 :: uu____1985  in
                    uu____1954 :: uu____1964  in
                  (FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                    "string", S) :: uu____1943
                   in
                (FStar_Parser_Const.unit_lid, (Prims.parse_int "0"), "unit",
                  S) :: uu____1932
                 in
              (FStar_Parser_Const.bool_lid, (Prims.parse_int "0"), "bool", S)
                :: uu____1921
               in
            (FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int", S) ::
              uu____1910
             in
          let is_known_type_constructor fv1 n1 =
            FStar_Util.for_some
              (fun uu____2238  ->
                 match uu____2238 with
                 | (x,args,uu____2249,uu____2250) ->
                     (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
              known_type_constructors
             in
          let find_env_entry bv uu____2265 =
            match uu____2265 with
            | (bv',uu____2271) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
          let rec mk_embedding env t2 =
            let uu____2295 =
              let uu____2296 = FStar_Syntax_Subst.compress t2  in
              uu____2296.FStar_Syntax_Syntax.n  in
            match uu____2295 with
            | FStar_Syntax_Syntax.Tm_name bv when
                FStar_Util.for_some (find_env_entry bv) env ->
                let uu____2304 =
                  let uu____2305 =
                    let uu____2310 =
                      FStar_Util.find_opt (find_env_entry bv) env  in
                    FStar_Util.must uu____2310  in
                  FStar_Pervasives_Native.snd uu____2305  in
                FStar_All.pipe_left mk_any_embedding uu____2304
            | FStar_Syntax_Syntax.Tm_refine (x,uu____2326) ->
                mk_embedding env x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t3,uu____2332,uu____2333) ->
                mk_embedding env t3
            | uu____2374 ->
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
                let uu____2376 = FStar_Syntax_Util.head_and_args t3  in
                (match uu____2376 with
                 | (head1,args) ->
                     let n_args = FStar_List.length args  in
                     let uu____2428 =
                       let uu____2429 = FStar_Syntax_Util.un_uinst head1  in
                       uu____2429.FStar_Syntax_Syntax.n  in
                     (match uu____2428 with
                      | FStar_Syntax_Syntax.Tm_refine (b,uu____2433) ->
                          mk_embedding env b.FStar_Syntax_Syntax.sort
                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                          is_known_type_constructor fv1 n_args ->
                          let arg_embeddings =
                            FStar_List.map
                              (fun uu____2455  ->
                                 match uu____2455 with
                                 | (t4,uu____2463) -> mk_embedding env t4)
                              args
                             in
                          let nm =
                            (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                             in
                          let uu____2469 =
                            let uu____2478 =
                              FStar_Util.find_opt
                                (fun uu____2502  ->
                                   match uu____2502 with
                                   | (x,uu____2512,uu____2513,uu____2514) ->
                                       FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                known_type_constructors
                               in
                            FStar_All.pipe_right uu____2478 FStar_Util.must
                             in
                          (match uu____2469 with
                           | (uu____2541,t_arity,trepr_head,loc_embedding) ->
                               let head2 =
                                 mk_basic_embedding loc_embedding nm  in
                               (match t_arity with
                                | _0_20 when _0_20 = (Prims.parse_int "0") ->
                                    head2
                                | n1 ->
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (head2, arg_embeddings))))
                      | uu____2549 ->
                          let uu____2550 =
                            let uu____2551 =
                              let uu____2552 =
                                FStar_Syntax_Print.term_to_string t3  in
                              Prims.strcat "Embedding not defined for type "
                                uu____2552
                               in
                            NoTacticEmbedding uu____2551  in
                          FStar_Exn.raise uu____2550))
             in
          let abstract_tvars tvar_names body =
            match tvar_names with
            | [] -> body
            | uu____2568 ->
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
                  let uu____2605 =
                    let uu____2606 =
                      let uu____2607 =
                        let uu____2614 =
                          let uu____2617 = str_to_name "args_tail"  in
                          [uu____2617]  in
                        (body, uu____2614)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2607  in
                    FStar_All.pipe_left w uu____2606  in
                  (pattern, FStar_Pervasives_Native.None, uu____2605)  in
                let default_branch =
                  let uu____2631 =
                    let uu____2632 =
                      let uu____2633 =
                        let uu____2640 = str_to_name "failwith"  in
                        let uu____2641 =
                          let uu____2644 =
                            let uu____2645 =
                              mlexpr_of_const FStar_Range.dummyRange
                                (FStar_Const.Const_string
                                   ("arity mismatch", FStar_Range.dummyRange))
                               in
                            FStar_All.pipe_left w uu____2645  in
                          [uu____2644]  in
                        (uu____2640, uu____2641)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2633  in
                    FStar_All.pipe_left w uu____2632  in
                  (FStar_Extraction_ML_Syntax.MLP_Wild,
                    FStar_Pervasives_Native.None, uu____2631)
                   in
                let body1 =
                  let uu____2651 =
                    let uu____2652 =
                      let uu____2667 = str_to_name "args"  in
                      (uu____2667, [branch1; default_branch])  in
                    FStar_Extraction_ML_Syntax.MLE_Match uu____2652  in
                  FStar_All.pipe_left w uu____2651  in
                mk_lam "args" body1
             in
          let uu____2702 = FStar_Syntax_Util.arrow_formals_comp t1  in
          match uu____2702 with
          | (bs,c) ->
              let result_typ = FStar_Syntax_Util.comp_result c  in
              let arity = FStar_List.length bs  in
              let uu____2755 =
                let uu____2776 =
                  FStar_Util.prefix_until
                    (fun uu____2818  ->
                       match uu____2818 with
                       | (b,uu____2826) ->
                           let uu____2831 =
                             let uu____2832 =
                               FStar_Syntax_Subst.compress
                                 b.FStar_Syntax_Syntax.sort
                                in
                             uu____2832.FStar_Syntax_Syntax.n  in
                           (match uu____2831 with
                            | FStar_Syntax_Syntax.Tm_type uu____2835 -> false
                            | uu____2836 -> true)) bs
                   in
                match uu____2776 with
                | FStar_Pervasives_Native.None  -> (bs, [])
                | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                    (tvars, (x :: rest))
                 in
              (match uu____2755 with
               | (type_vars,bs1) ->
                   let non_tvar_arity = FStar_List.length bs1  in
                   let tvar_names =
                     FStar_List.mapi
                       (fun i  ->
                          fun tv  ->
                            let uu____3073 = FStar_Util.string_of_int i  in
                            Prims.strcat "tv_" uu____3073) type_vars
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
                         let uu____3177 = FStar_Syntax_Util.is_pure_comp c
                            in
                         if uu____3177
                         then
                           let embed_fun_N =
                             mk_arrow_embedding non_tvar_arity  in
                           let args =
                             let uu____3196 =
                               let uu____3199 =
                                 let uu____3202 = lid_to_top_name fv  in
                                 [uu____3202]  in
                               res_embedding :: uu____3199  in
                             FStar_List.append arg_unembeddings uu____3196
                              in
                           let fun_embedding =
                             FStar_All.pipe_left w
                               (FStar_Extraction_ML_Syntax.MLE_App
                                  (embed_fun_N, args))
                              in
                           let tabs = abstract_tvars tvar_names fun_embedding
                              in
                           let uu____3207 =
                             let uu____3214 = mk_lam "_psc" tabs  in
                             (uu____3214, arity, true)  in
                           FStar_Pervasives_Native.Some uu____3207
                         else
                           (let uu____3226 =
                              let uu____3227 =
                                FStar_TypeChecker_Env.norm_eff_name tcenv
                                  (FStar_Syntax_Util.comp_effect_name c)
                                 in
                              FStar_Ident.lid_equals uu____3227
                                FStar_Parser_Const.effect_TAC_lid
                               in
                            if uu____3226
                            then
                              let h =
                                let uu____3237 =
                                  let uu____3238 =
                                    FStar_Util.string_of_int non_tvar_arity
                                     in
                                  Prims.strcat
                                    "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
                                    uu____3238
                                   in
                                str_to_top_name uu____3237  in
                              let tac_fun =
                                let uu____3246 =
                                  let uu____3247 =
                                    let uu____3254 =
                                      let uu____3255 =
                                        let uu____3256 =
                                          FStar_Util.string_of_int
                                            non_tvar_arity
                                           in
                                        Prims.strcat
                                          "FStar_Tactics_Native.from_tactic_"
                                          uu____3256
                                         in
                                      str_to_top_name uu____3255  in
                                    let uu____3263 =
                                      let uu____3266 = lid_to_top_name fv  in
                                      [uu____3266]  in
                                    (uu____3254, uu____3263)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3247
                                   in
                                FStar_All.pipe_left w uu____3246  in
                              let tac_lid_app =
                                let uu____3270 =
                                  let uu____3271 =
                                    let uu____3278 =
                                      str_to_top_name
                                        "FStar_Ident.lid_of_str"
                                       in
                                    (uu____3278, [w ml_fv])  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3271
                                   in
                                FStar_All.pipe_left w uu____3270  in
                              let psc = str_to_name "psc"  in
                              let all_args = str_to_name "args"  in
                              let args =
                                let uu____3286 =
                                  let uu____3289 =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_Bool
                                            true))
                                     in
                                  [uu____3289; tac_fun]  in
                                FStar_List.append uu____3286
                                  (FStar_List.append arg_unembeddings
                                     [res_embedding; tac_lid_app; psc])
                                 in
                              let tabs =
                                match tvar_names with
                                | [] ->
                                    let uu____3291 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h,
                                             (FStar_List.append args
                                                [all_args])))
                                       in
                                    mk_lam "args" uu____3291
                                | uu____3294 ->
                                    let uu____3297 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h, args))
                                       in
                                    abstract_tvars tvar_names uu____3297
                                 in
                              let uu____3300 =
                                let uu____3307 = mk_lam "psc" tabs  in
                                (uu____3307, (arity + (Prims.parse_int "1")),
                                  false)
                                 in
                              FStar_Pervasives_Native.Some uu____3300
                            else
                              (let uu____3321 =
                                 let uu____3322 =
                                   let uu____3323 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   Prims.strcat
                                     "Plugins not defined for type "
                                     uu____3323
                                    in
                                 NoTacticEmbedding uu____3322  in
                               FStar_Exn.raise uu____3321))
                     | (b,uu____3333)::bs3 ->
                         let uu____3353 =
                           let uu____3356 =
                             mk_embedding env b.FStar_Syntax_Syntax.sort  in
                           uu____3356 :: accum_embeddings  in
                         aux uu____3353 env bs3
                      in
                   (try
                      (fun uu___262_3366  ->
                         match () with | () -> aux [] tvar_context bs1) ()
                    with
                    | NoTacticEmbedding msg ->
                        ((let uu____3389 = FStar_Ident.string_of_lid fv  in
                          not_implemented_warning t1.FStar_Syntax_Syntax.pos
                            uu____3389 msg);
                         FStar_Pervasives_Native.None)))
  