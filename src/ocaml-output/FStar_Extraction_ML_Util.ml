open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____67915  ->
    let uu____67916 = FStar_Options.codegen ()  in
    uu____67916 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____67985 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____68015) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____68021) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____68026 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____68030 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_68044  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_68047 ->
          let uu____68048 =
            let uu____68050 = FStar_Range.string_of_range p  in
            let uu____68052 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____68050 uu____68052
             in
          failwith uu____68048
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____68069 =
        let uu____68070 =
          let uu____68071 =
            let uu____68083 = FStar_Util.string_of_int i  in
            (uu____68083, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____68071  in
        FStar_All.pipe_right uu____68070
          (fun _68096  -> FStar_Extraction_ML_Syntax.MLE_Const _68096)
         in
      FStar_All.pipe_right uu____68069
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____68105 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _68106  -> FStar_Extraction_ML_Syntax.MLE_Const _68106)
         in
      FStar_All.pipe_right uu____68105
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____68107 =
      let uu____68114 =
        let uu____68117 =
          let uu____68118 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____68118 cstr  in
        let uu____68121 =
          let uu____68124 =
            let uu____68125 =
              let uu____68127 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____68127 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____68125 cint  in
          let uu____68130 =
            let uu____68133 =
              let uu____68134 =
                let uu____68136 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____68136 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____68134 cint  in
            let uu____68139 =
              let uu____68142 =
                let uu____68143 =
                  let uu____68145 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____68145 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____68143 cint  in
              let uu____68148 =
                let uu____68151 =
                  let uu____68152 =
                    let uu____68154 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____68154 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____68152 cint  in
                [uu____68151]  in
              uu____68142 :: uu____68148  in
            uu____68133 :: uu____68139  in
          uu____68124 :: uu____68130  in
        uu____68117 :: uu____68121  in
      (mk_range_mle, uu____68114)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____68107
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____68171 ->
          let uu____68172 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____68172
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____68200 =
            FStar_Util.find_opt
              (fun uu____68216  ->
                 match uu____68216 with | (y,uu____68224) -> y = x) subst1
             in
          (match uu____68200 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____68248 =
            let uu____68255 = subst_aux subst1 t1  in
            let uu____68256 = subst_aux subst1 t2  in
            (uu____68255, f, uu____68256)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____68248
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____68263 =
            let uu____68270 = FStar_List.map (subst_aux subst1) args  in
            (uu____68270, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____68263
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____68278 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____68278
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____68294  ->
    fun args  ->
      match uu____68294 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____68308 =
               let uu____68309 = FStar_List.zip formals args  in
               subst_aux uu____68309 t  in
             FStar_Pervasives_Native.Some uu____68308)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____68341 = try_subst ts args  in
      match uu____68341 with
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
    fun uu___617_68358  ->
      match uu___617_68358 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____68367 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____68367 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____68373 = try_subst ts args  in
               (match uu____68373 with
                | FStar_Pervasives_Native.None  ->
                    let uu____68378 =
                      let uu____68380 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____68382 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____68384 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____68380 uu____68382 uu____68384
                       in
                    failwith uu____68378
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____68391 -> FStar_Pervasives_Native.None)
      | uu____68394 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____68408) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____68412 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_68424  ->
    match uu___618_68424 with
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
        | uu____68445 ->
            let uu____68450 =
              let uu____68452 = FStar_Range.string_of_range r  in
              let uu____68454 = eff_to_string f  in
              let uu____68456 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____68452
                uu____68454 uu____68456
               in
            failwith uu____68450
  
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
    (fun uu____68499  ->
       fun t  ->
         match uu____68499 with
         | (uu____68506,t0) ->
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
                | uu____68634 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____68671 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____68679 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____68679 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____68690;
                     FStar_Extraction_ML_Syntax.loc = uu____68691;_}
                   ->
                   let uu____68716 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____68716
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____68737 = type_leq unfold_ty t2 t2'  in
                        (if uu____68737
                         then
                           let body1 =
                             let uu____68751 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____68751
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____68759 =
                             let uu____68762 =
                               let uu____68763 =
                                 let uu____68768 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____68768
                                  in
                               FStar_All.pipe_left uu____68763
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____68762  in
                           (true, uu____68759)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____68808 =
                           let uu____68816 =
                             let uu____68819 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _68822  ->
                                  FStar_Pervasives_Native.Some _68822)
                               uu____68819
                              in
                           type_leq_c unfold_ty uu____68816 t2 t2'  in
                         match uu____68808 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____68847 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____68847
                               | uu____68858 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____68870 ->
                   let uu____68873 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____68873
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____68919 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____68919
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____68944 = unfold_ty t  in
                 match uu____68944 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____68959 = unfold_ty t'  in
                     (match uu____68959 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____68984 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____68984
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____69011,uu____69012)
              ->
              let uu____69019 = unfold_ty t  in
              (match uu____69019 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____69034 -> (false, FStar_Pervasives_Native.None))
          | (uu____69041,FStar_Extraction_ML_Syntax.MLTY_Named uu____69042)
              ->
              let uu____69049 = unfold_ty t'  in
              (match uu____69049 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____69064 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____69075 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____69090 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____69090 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____69121 =
          let uu____69128 = erase_effect_annotations t1  in
          let uu____69129 = erase_effect_annotations t2  in
          (uu____69128, FStar_Extraction_ML_Syntax.E_PURE, uu____69129)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____69121
    | uu____69130 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_69158  ->
    match uu___619_69158 with
    | (FStar_Util.Inl uu____69170,uu____69171)::uu____69172 -> true
    | uu____69196 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____69224  ->
    match uu____69224 with
    | (ns,n1) ->
        let uu____69246 =
          let uu____69248 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____69248  in
        if uu____69246
        then
          let uu____69258 =
            let uu____69260 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____69260  in
          FStar_Pervasives_Native.Some uu____69258
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____69279 = is_xtuple mlp  in
        (match uu____69279 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____69286 -> e)
    | uu____69290 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_69301  ->
    match uu___620_69301 with
    | f::uu____69308 ->
        let uu____69311 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____69311 with
         | (ns,uu____69322) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____69335 -> failwith "impos"
  
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
  fun uu____69401  ->
    match uu____69401 with
    | (ns,n1) ->
        let uu____69423 =
          let uu____69425 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____69425  in
        if uu____69423
        then
          let uu____69435 =
            let uu____69437 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____69437  in
          FStar_Pervasives_Native.Some uu____69435
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____69456 = is_xtuple_ty mlp  in
        (match uu____69456 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____69463 -> t)
    | uu____69467 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____69481 = codegen_fsharp ()  in
    if uu____69481
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____69503  ->
    match uu____69503 with
    | (ns,n1) ->
        let uu____69523 = codegen_fsharp ()  in
        if uu____69523
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____69551 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____69551, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____69585 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____69585
      then true
      else
        (let uu____69592 = unfold_ty t  in
         match uu____69592 with
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
            let uu____69622 =
              let uu____69629 = eraseTypeDeep unfold_ty tyd  in
              let uu____69633 = eraseTypeDeep unfold_ty tycd  in
              (uu____69629, etag, uu____69633)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____69622
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____69645 = erasableType unfold_ty t  in
          if uu____69645
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____69653 =
               let uu____69660 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____69660, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____69653)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____69671 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____69671
      | uu____69677 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____69688 =
    let uu____69693 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____69693  in
  FStar_All.pipe_left uu____69688
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
          let uu____69781 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____69781
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____69797 = FStar_Range.file_of_range r  in (line, uu____69797)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69820,b) ->
        let uu____69822 = doms_and_cod b  in
        (match uu____69822 with | (ds,c) -> ((a :: ds), c))
    | uu____69843 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____69856 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____69856
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69884,b) ->
        let uu____69886 = uncurry_mlty_fun b  in
        (match uu____69886 with | (args,res) -> ((a :: args), res))
    | uu____69907 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____69923 -> true
    | uu____69926 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____69937 -> uu____69937
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____69959 =
          let uu____69965 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____69965)  in
        FStar_Errors.log_issue r uu____69959
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____69978 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____69989 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____70000 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____70011 -> false
  
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
              let uu____70082 =
                let uu____70083 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____70083  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70082
               in
            let lid_to_top_name l =
              let uu____70090 =
                let uu____70091 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____70091  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70090
               in
            let str_to_name s =
              let uu____70100 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____70100  in
            let str_to_top_name s =
              let uu____70109 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____70109  in
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
              let uu____70147 =
                let uu____70148 =
                  let uu____70155 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____70157 =
                    let uu____70160 =
                      let uu____70161 =
                        let uu____70162 =
                          let uu____70163 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____70163
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____70162  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____70161
                       in
                    [uu____70160]  in
                  (uu____70155, uu____70157)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70148  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70147
               in
            let emb_prefix uu___621_70178 =
              match uu___621_70178 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____70192 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____70203 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____70232 =
                let uu____70234 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____70234  in
              emb_prefix l uu____70232  in
            let mk_any_embedding l s =
              let uu____70250 =
                let uu____70251 =
                  let uu____70258 = emb_prefix l "mk_any_emb"  in
                  let uu____70260 =
                    let uu____70263 = str_to_name s  in [uu____70263]  in
                  (uu____70258, uu____70260)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70251  in
              FStar_All.pipe_left w uu____70250  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____70313 =
                let uu____70314 =
                  let uu____70321 = emb_prefix l "e_arrow"  in
                  (uu____70321, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70314  in
              FStar_All.pipe_left w uu____70313  in
            let known_type_constructors =
              let term_cs =
                let uu____70359 =
                  let uu____70374 =
                    let uu____70389 =
                      let uu____70404 =
                        let uu____70419 =
                          let uu____70434 =
                            let uu____70449 =
                              let uu____70464 =
                                let uu____70477 =
                                  let uu____70486 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____70486, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____70477, Syntax_term)  in
                              let uu____70500 =
                                let uu____70515 =
                                  let uu____70528 =
                                    let uu____70537 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____70537, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____70528, Refl_emb)  in
                                let uu____70551 =
                                  let uu____70566 =
                                    let uu____70579 =
                                      let uu____70588 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____70588, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____70579, Refl_emb)  in
                                  let uu____70602 =
                                    let uu____70617 =
                                      let uu____70630 =
                                        let uu____70639 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____70639, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____70630, Refl_emb)  in
                                    let uu____70653 =
                                      let uu____70668 =
                                        let uu____70681 =
                                          let uu____70690 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____70690,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____70681, Refl_emb)  in
                                      let uu____70704 =
                                        let uu____70719 =
                                          let uu____70732 =
                                            let uu____70741 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____70741,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____70732, Refl_emb)  in
                                        [uu____70719]  in
                                      uu____70668 :: uu____70704  in
                                    uu____70617 :: uu____70653  in
                                  uu____70566 :: uu____70602  in
                                uu____70515 :: uu____70551  in
                              uu____70464 :: uu____70500  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____70449
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____70434
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____70419
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____70404
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____70389
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____70374
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____70359
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_71048  ->
                     match uu___622_71048 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____71123 -> failwith "Impossible") term_cs
                 in
              fun uu___623_71149  ->
                match uu___623_71149 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____71164 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____71201  ->
                   match uu____71201 with
                   | ((x,args,uu____71217),uu____71218) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____71248 =
              match uu____71248 with
              | (bv',uu____71256) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____71290 =
                let uu____71291 = FStar_Syntax_Subst.compress t3  in
                uu____71291.FStar_Syntax_Syntax.n  in
              match uu____71290 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____71300 =
                    let uu____71302 =
                      let uu____71308 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____71308  in
                    FStar_Pervasives_Native.snd uu____71302  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____71300
              | FStar_Syntax_Syntax.Tm_refine (x,uu____71329) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____71335,uu____71336)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____71409 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____71409 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____71431 =
                           let uu____71432 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____71432  in
                         uu____71431.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____71450 = mk_embedding l env t0  in
                       let uu____71451 = mk_embedding l env t11  in
                       emb_arrow l uu____71450 uu____71451)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____71522 =
                      let uu____71529 =
                        let uu____71530 =
                          let uu____71545 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____71545)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____71530  in
                      FStar_Syntax_Syntax.mk uu____71529  in
                    uu____71522 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____71573 ->
                  let uu____71574 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71574 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71626 =
                         let uu____71627 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71627.FStar_Syntax_Syntax.n  in
                       (match uu____71626 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71657  ->
                                      match uu____71657 with
                                      | (t4,uu____71665) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71672 =
                              let uu____71685 =
                                FStar_Util.find_opt
                                  (fun uu____71717  ->
                                     match uu____71717 with
                                     | ((x,uu____71732,uu____71733),uu____71734)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71685
                                FStar_Util.must
                               in
                            (match uu____71672 with
                             | ((uu____71785,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _71802 when
                                      _71802 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____71807 ->
                            let uu____71808 =
                              let uu____71809 =
                                let uu____71811 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____71811
                                 in
                              NoTacticEmbedding uu____71809  in
                            FStar_Exn.raise uu____71808))
              | FStar_Syntax_Syntax.Tm_uinst uu____71814 ->
                  let uu____71821 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71821 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71873 =
                         let uu____71874 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71874.FStar_Syntax_Syntax.n  in
                       (match uu____71873 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71904  ->
                                      match uu____71904 with
                                      | (t4,uu____71912) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71919 =
                              let uu____71932 =
                                FStar_Util.find_opt
                                  (fun uu____71964  ->
                                     match uu____71964 with
                                     | ((x,uu____71979,uu____71980),uu____71981)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71932
                                FStar_Util.must
                               in
                            (match uu____71919 with
                             | ((uu____72032,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72049 when
                                      _72049 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72054 ->
                            let uu____72055 =
                              let uu____72056 =
                                let uu____72058 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72058
                                 in
                              NoTacticEmbedding uu____72056  in
                            FStar_Exn.raise uu____72055))
              | FStar_Syntax_Syntax.Tm_app uu____72061 ->
                  let uu____72078 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____72078 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____72130 =
                         let uu____72131 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____72131.FStar_Syntax_Syntax.n  in
                       (match uu____72130 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____72161  ->
                                      match uu____72161 with
                                      | (t4,uu____72169) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____72176 =
                              let uu____72189 =
                                FStar_Util.find_opt
                                  (fun uu____72221  ->
                                     match uu____72221 with
                                     | ((x,uu____72236,uu____72237),uu____72238)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____72189
                                FStar_Util.must
                               in
                            (match uu____72176 with
                             | ((uu____72289,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72306 when
                                      _72306 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72311 ->
                            let uu____72312 =
                              let uu____72313 =
                                let uu____72315 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72315
                                 in
                              NoTacticEmbedding uu____72313  in
                            FStar_Exn.raise uu____72312))
              | uu____72318 ->
                  let uu____72319 =
                    let uu____72320 =
                      let uu____72322 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____72322
                       in
                    NoTacticEmbedding uu____72320  in
                  FStar_Exn.raise uu____72319
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____72344 =
                      let uu____72345 =
                        let uu____72352 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72354 =
                          let uu____72357 =
                            let uu____72358 =
                              let uu____72359 =
                                let uu____72360 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72360
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72359
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72358
                             in
                          let uu____72362 =
                            let uu____72365 =
                              let uu____72366 =
                                let uu____72367 =
                                  let uu____72368 =
                                    let uu____72375 =
                                      let uu____72378 = str_to_name "args"
                                         in
                                      [uu____72378]  in
                                    (body, uu____72375)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____72368
                                   in
                                FStar_All.pipe_left w uu____72367  in
                              mk_lam "_" uu____72366  in
                            [uu____72365]  in
                          uu____72357 :: uu____72362  in
                        (uu____72352, uu____72354)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72345  in
                    FStar_All.pipe_left w uu____72344  in
                  mk_lam "args" body1
              | uu____72386 ->
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
                    let uu____72435 =
                      let uu____72436 =
                        let uu____72437 =
                          let uu____72444 =
                            let uu____72447 = str_to_name "args"  in
                            [uu____72447]  in
                          (body, uu____72444)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72437  in
                      FStar_All.pipe_left w uu____72436  in
                    (pattern, FStar_Pervasives_Native.None, uu____72435)  in
                  let default_branch =
                    let uu____72462 =
                      let uu____72463 =
                        let uu____72464 =
                          let uu____72471 = str_to_name "failwith"  in
                          let uu____72473 =
                            let uu____72476 =
                              let uu____72477 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____72477  in
                            [uu____72476]  in
                          (uu____72471, uu____72473)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72464  in
                      FStar_All.pipe_left w uu____72463  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____72462)
                     in
                  let body1 =
                    let uu____72485 =
                      let uu____72486 =
                        let uu____72501 = str_to_name "args"  in
                        (uu____72501, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____72486  in
                    FStar_All.pipe_left w uu____72485  in
                  let body2 =
                    let uu____72538 =
                      let uu____72539 =
                        let uu____72546 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72548 =
                          let uu____72551 =
                            let uu____72552 =
                              let uu____72553 =
                                let uu____72554 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72554
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72553
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72552
                             in
                          let uu____72556 =
                            let uu____72559 = mk_lam "_" body1  in
                            [uu____72559]  in
                          uu____72551 :: uu____72556  in
                        (uu____72546, uu____72548)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72539  in
                    FStar_All.pipe_left w uu____72538  in
                  mk_lam "args" body2
               in
            let uu____72564 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____72564 with
            | (bs,c) ->
                let uu____72597 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____72698 = FStar_Util.first_N n1 bs  in
                           match uu____72698 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____72776 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____72776
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____72793 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____72795 = FStar_Util.string_of_int n1
                                in
                             let uu____72797 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____72793 uu____72795 uu____72797
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____72597 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____72854 =
                       let uu____72875 =
                         FStar_Util.prefix_until
                           (fun uu____72917  ->
                              match uu____72917 with
                              | (b,uu____72926) ->
                                  let uu____72931 =
                                    let uu____72932 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____72932.FStar_Syntax_Syntax.n  in
                                  (match uu____72931 with
                                   | FStar_Syntax_Syntax.Tm_type uu____72936
                                       -> false
                                   | uu____72938 -> true)) bs1
                          in
                       match uu____72875 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____72854 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____73180 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____73180) type_vars
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
                                let uu____73280 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____73280
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____73301 =
                                      let uu____73304 =
                                        let uu____73307 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____73308 =
                                          let uu____73311 =
                                            let uu____73312 =
                                              let uu____73313 =
                                                let uu____73314 =
                                                  let uu____73326 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____73326,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____73314
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____73313
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____73312
                                             in
                                          [uu____73311; fv_lid_embedded; cb]
                                           in
                                        uu____73307 :: uu____73308  in
                                      res_embedding :: uu____73304  in
                                    FStar_List.append arg_unembeddings
                                      uu____73301
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
                                  let uu____73351 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____73351, arity, true)
                                else
                                  (let uu____73365 =
                                     let uu____73367 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____73367
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____73365
                                   then
                                     let h =
                                       let uu____73378 =
                                         let uu____73380 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____73380
                                          in
                                       str_to_top_name uu____73378  in
                                     let tac_fun =
                                       let uu____73389 =
                                         let uu____73390 =
                                           let uu____73397 =
                                             let uu____73398 =
                                               let uu____73400 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____73400
                                                in
                                             str_to_top_name uu____73398  in
                                           let uu____73408 =
                                             let uu____73411 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____73411]  in
                                           (uu____73397, uu____73408)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____73390
                                          in
                                       FStar_All.pipe_left w uu____73389  in
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
                                           let uu____73425 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____73425
                                       | uu____73429 ->
                                           let uu____73433 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____73433
                                        in
                                     let uu____73436 =
                                       let uu____73437 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____73437  in
                                     (uu____73436,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____73452 =
                                        let uu____73453 =
                                          let uu____73455 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____73455
                                           in
                                        NoTacticEmbedding uu____73453  in
                                      FStar_Exn.raise uu____73452))
                            | (b,uu____73467)::bs4 ->
                                let uu____73487 =
                                  let uu____73490 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____73490 :: accum_embeddings  in
                                aux loc uu____73487 bs4
                             in
                          (try
                             (fun uu___1304_73512  ->
                                match () with
                                | () ->
                                    let uu____73525 = aux Syntax_term [] bs2
                                       in
                                    (match uu____73525 with
                                     | (w1,a,b) ->
                                         let uu____73553 = aux NBE_t [] bs2
                                            in
                                         (match uu____73553 with
                                          | (w',uu____73575,uu____73576) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____73612 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____73612 msg);
                                FStar_Pervasives_Native.None))))
  