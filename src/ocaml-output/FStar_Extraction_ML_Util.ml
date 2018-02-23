open Prims
let (codegen_fsharp : Prims.unit -> Prims.bool) =
  fun uu____3  ->
    let uu____4 = FStar_Options.codegen ()  in
    uu____4 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
  
let (mlconst_of_const' :
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant) =
  fun sctt  ->
    match sctt with
    | FStar_Const.Const_effect  -> failwith "Unsupported constant"
    | FStar_Const.Const_range uu____47 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____72) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____78) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____79 ->
        failwith "Unhandled constant: reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const' c
      with
      | uu____92 ->
          let uu____93 =
            let uu____94 = FStar_Range.string_of_range p  in
            let uu____95 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____94 uu____95
             in
          failwith uu____93
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____103 =
        let uu____104 =
          let uu____105 =
            let uu____116 = FStar_Util.string_of_int i  in
            (uu____116, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____105  in
        FStar_All.pipe_right uu____104
          (fun _0_41  -> FStar_Extraction_ML_Syntax.MLE_Const _0_41)
         in
      FStar_All.pipe_right uu____103
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____131 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_42  -> FStar_Extraction_ML_Syntax.MLE_Const _0_42)
         in
      FStar_All.pipe_right uu____131
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____132 =
      let uu____139 =
        let uu____142 =
          let uu____143 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____143 cstr  in
        let uu____144 =
          let uu____147 =
            let uu____148 =
              let uu____149 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____149 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____148 cint  in
          let uu____150 =
            let uu____153 =
              let uu____154 =
                let uu____155 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____155 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____154 cint  in
            let uu____156 =
              let uu____159 =
                let uu____160 =
                  let uu____161 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____161 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____160 cint  in
              let uu____162 =
                let uu____165 =
                  let uu____166 =
                    let uu____167 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____167 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____166 cint  in
                [uu____165]  in
              uu____159 :: uu____162  in
            uu____153 :: uu____156  in
          uu____147 :: uu____150  in
        uu____142 :: uu____144  in
      (mk_range_mle, uu____139)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____132
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____177 ->
          let uu____178 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____178
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____198 =
            FStar_Util.find_opt
              (fun uu____212  ->
                 match uu____212 with | (y,uu____218) -> y = x) subst1
             in
          (match uu____198 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____235 =
            let uu____242 = subst_aux subst1 t1  in
            let uu____243 = subst_aux subst1 t2  in (uu____242, f, uu____243)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____235
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____250 =
            let uu____257 = FStar_List.map (subst_aux subst1) args  in
            (uu____257, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____250
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____265 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____265
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____276  ->
    fun args  ->
      match uu____276 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____287 =
               let uu____288 = FStar_List.zip formals args  in
               subst_aux uu____288 t  in
             FStar_Pervasives_Native.Some uu____287)
  
let (subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____305 = try_subst ts args  in
      match uu____305 with
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
    fun uu___59_316  ->
      match uu___59_316 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____325 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____325 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____331 = try_subst ts args  in
               (match uu____331 with
                | FStar_Pervasives_Native.None  ->
                    let uu____336 =
                      let uu____337 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____338 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____339 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____337 uu____338 uu____339
                       in
                    failwith uu____336
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____343 -> FStar_Pervasives_Native.None)
      | uu____346 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____353) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____354 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___60_361  ->
    match uu___60_361 with
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
        | uu____371 ->
            let uu____376 =
              let uu____377 = FStar_Range.string_of_range r  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____377
                (eff_to_string f) (eff_to_string f')
               in
            failwith uu____376
  
let (join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
  
let mk_ty_fun :
  'Auu____391 .
    Prims.unit ->
      ('Auu____391,FStar_Extraction_ML_Syntax.mlty)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____402  ->
    FStar_List.fold_right
      (fun uu____411  ->
         fun t  ->
           match uu____411 with
           | (uu____417,t0) ->
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
                | uu____504 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____536 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____543 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty
                       in
                    FStar_Extraction_ML_Syntax.with_ty uu____543 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____553;
                     FStar_Extraction_ML_Syntax.loc = uu____554;_}
                   ->
                   let uu____575 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____575
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____591 = type_leq unfold_ty t2 t2'  in
                        (if uu____591
                         then
                           let body1 =
                             let uu____602 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____602
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____607 =
                             let uu____610 =
                               let uu____611 =
                                 let uu____614 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____614
                                  in
                               FStar_All.pipe_left uu____611
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____610  in
                           (true, uu____607)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____643 =
                           let uu____650 =
                             let uu____653 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_43  ->
                                  FStar_Pervasives_Native.Some _0_43)
                               uu____653
                              in
                           type_leq_c unfold_ty uu____650 t2 t2'  in
                         match uu____643 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____677 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____677
                               | uu____686 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____694 ->
                   let uu____697 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____697
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____733 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____733
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____749 = unfold_ty t  in
                 match uu____749 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____763 = unfold_ty t'  in
                     (match uu____763 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____785 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____785
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____802,uu____803) ->
              let uu____810 = unfold_ty t  in
              (match uu____810 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____824 -> (false, FStar_Pervasives_Native.None))
          | (uu____829,FStar_Extraction_ML_Syntax.MLTY_Named uu____830) ->
              let uu____837 = unfold_ty t'  in
              (match uu____837 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____851 -> (false, FStar_Pervasives_Native.None))
          | uu____856 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____867 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____867 FStar_Pervasives_Native.fst

let is_type_abstraction :
  'Auu____889 'Auu____890 'Auu____891 .
    (('Auu____891,'Auu____890) FStar_Util.either,'Auu____889)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun uu___61_905  ->
    match uu___61_905 with
    | (FStar_Util.Inl uu____916,uu____917)::uu____918 -> true
    | uu____941 -> false
  
let (is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____962  ->
    match uu____962 with
    | (ns,n1) ->
        let uu____977 =
          let uu____978 = FStar_Util.concat_l "." (FStar_List.append ns [n1])
             in
          FStar_Parser_Const.is_tuple_datacon_string uu____978  in
        if uu____977
        then
          let uu____981 =
            let uu____982 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____982  in
          FStar_Pervasives_Native.Some uu____981
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____993 = is_xtuple mlp  in
        (match uu____993 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____997 -> e)
    | uu____1000 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___62_1007  ->
    match uu___62_1007 with
    | f::uu____1013 ->
        let uu____1016 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1016 with
         | (ns,uu____1026) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1037 -> failwith "impos"
  
let record_fields :
  'Auu____1045 .
    FStar_Ident.lident Prims.list ->
      'Auu____1045 Prims.list ->
        (Prims.string,'Auu____1045) FStar_Pervasives_Native.tuple2 Prims.list
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
  fun uu____1086  ->
    match uu____1086 with
    | (ns,n1) ->
        let uu____1101 =
          let uu____1102 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1102  in
        if uu____1101
        then
          let uu____1105 =
            let uu____1106 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1106  in
          FStar_Pervasives_Native.Some uu____1105
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1117 = is_xtuple_ty mlp  in
        (match uu____1117 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1121 -> t)
    | uu____1124 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1132 = codegen_fsharp ()  in
    if uu____1132
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1142  ->
    match uu____1142 with
    | (ns,n1) ->
        let uu____1155 = codegen_fsharp ()  in
        if uu____1155
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____1166 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1166, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1186 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1186
      then true
      else
        (let uu____1188 = unfold_ty t  in
         match uu____1188 with
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
            let uu____1208 =
              let uu____1215 = eraseTypeDeep unfold_ty tyd  in
              let uu____1219 = eraseTypeDeep unfold_ty tycd  in
              (uu____1215, etag, uu____1219)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1208
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1230 = erasableType unfold_ty t  in
          if uu____1230
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1235 =
               let uu____1242 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1242, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1235)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1253 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1253
      | uu____1259 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1262 =
    let uu____1265 =
      (mk_ty_fun ())
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1265  in
  FStar_All.pipe_left uu____1262
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
          let uu____1330 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1330
  
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1340 = FStar_Range.file_of_range r  in (line, uu____1340)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1357,b) ->
        let uu____1359 = doms_and_cod b  in
        (match uu____1359 with | (ds,c) -> ((a :: ds), c))
    | uu____1380 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1390 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1390
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1415,b) ->
        let uu____1417 = uncurry_mlty_fun b  in
        (match uu____1417 with | (args,res) -> ((a :: args), res))
    | uu____1438 -> ([], t)
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> Prims.unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1450 =
          let uu____1455 =
            FStar_Util.format2
              ". Tactic %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1455)  in
        FStar_Errors.log_issue r uu____1450
  
type emb_decl =
  | Embed 
  | Unembed [@@deriving show]
let (uu___is_Embed : emb_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____1459 -> false
  
let (uu___is_Unembed : emb_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____1463 -> false
  
let (lid_to_name : FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun l  ->
    let uu____1467 = FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
    FStar_Extraction_ML_Syntax.MLE_Name uu____1467
  
let (lid_to_top_name :
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun l  ->
    let uu____1471 =
      let uu____1472 = FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
      FStar_Extraction_ML_Syntax.MLE_Name uu____1472  in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1471
  
let (str_to_name : Prims.string -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun s  ->
    let uu____1476 = FStar_Ident.lid_of_str s  in lid_to_name uu____1476
  
let (str_to_top_name : Prims.string -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun s  ->
    let uu____1480 = FStar_Ident.lid_of_str s  in lid_to_top_name uu____1480
  
let (fstar_syn_syn_prefix :
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun s  -> str_to_name (Prims.strcat "FStar_Syntax_Syntax." s) 
let (fstar_tc_common_prefix :
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun s  -> str_to_name (Prims.strcat "FStar_TypeChecker_Common." s) 
let (fstar_refl_basic_prefix :
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Basic." s) 
let (fstar_refl_data_prefix :
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Data." s) 
let (fstar_emb_basic_prefix :
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun s  -> str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s) 
let (mk_basic_embedding :
  emb_decl -> Prims.string -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun m  ->
    fun s  ->
      match m with
      | Embed  -> fstar_emb_basic_prefix (Prims.strcat "embed_" s)
      | Unembed  -> fstar_emb_basic_prefix (Prims.strcat "unembed_" s)
  
let (mk_embedding :
  emb_decl -> Prims.string -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun m  ->
    fun s  ->
      match m with
      | Embed  -> fstar_refl_basic_prefix (Prims.strcat "embed_" s)
      | Unembed  -> fstar_refl_basic_prefix (Prims.strcat "unembed_" s)
  
let (mk_tactic_unembedding :
  FStar_Extraction_ML_Syntax.mlexpr' Prims.list ->
    FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun args  ->
    let tac_arg = "t"  in
    let reify_tactic =
      let uu____1517 =
        let uu____1518 =
          let uu____1525 =
            str_to_top_name "FStar_Tactics_Interpreter.reify_tactic"  in
          let uu____1526 =
            let uu____1529 = str_to_top_name tac_arg  in [uu____1529]  in
          (uu____1525, uu____1526)  in
        FStar_Extraction_ML_Syntax.MLE_App uu____1518  in
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1517
       in
    let from_tac =
      let uu____1533 =
        let uu____1534 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1"))
           in
        Prims.strcat "FStar_Tactics_Builtins.from_tac_" uu____1534  in
      str_to_top_name uu____1533  in
    let unembed_tactic =
      let uu____1536 =
        let uu____1537 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1"))
           in
        Prims.strcat "FStar_Tactics_Interpreter.unembed_tactic_" uu____1537
         in
      str_to_top_name uu____1536  in
    let app =
      match FStar_List.length args with
      | _0_44 when _0_44 = (Prims.parse_int "1") ->
          let uu____1539 =
            let uu____1546 =
              let uu____1549 =
                let uu____1550 =
                  let uu____1551 =
                    let uu____1558 =
                      let uu____1561 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) args
                         in
                      FStar_List.append uu____1561 [reify_tactic]  in
                    (unembed_tactic, uu____1558)  in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1551  in
                FStar_Extraction_ML_Syntax.with_ty
                  FStar_Extraction_ML_Syntax.MLTY_Top uu____1550
                 in
              [uu____1549]  in
            (from_tac, uu____1546)  in
          FStar_Extraction_ML_Syntax.MLE_App uu____1539
      | n1 ->
          let uu____1569 =
            let uu____1574 =
              let uu____1575 = FStar_Util.string_of_int n1  in
              FStar_Util.format1
                "Unembedding not defined for tactics of %s arguments\n"
                uu____1575
               in
            (FStar_Errors.Fatal_CallNotImplemented, uu____1574)  in
          FStar_Errors.raise_err uu____1569
       in
    FStar_Extraction_ML_Syntax.MLE_Fun
      ([(tac_arg, FStar_Extraction_ML_Syntax.MLTY_Top);
       ("()", FStar_Extraction_ML_Syntax.MLTY_Top)],
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top app))
  
let rec (mk_tac_param_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun tcenv  ->
    fun t  ->
      let rec try_mk t1 unrefined =
        let uu____1613 =
          let uu____1614 = FStar_Syntax_Subst.compress t1  in
          uu____1614.FStar_Syntax_Syntax.n  in
        match uu____1613 with
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
            fstar_syn_syn_prefix "t_int"
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
            fstar_syn_syn_prefix "t_bool"
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
            fstar_syn_syn_prefix "t_unit"
        | FStar_Syntax_Syntax.Tm_fvar fv when
            FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid ->
            fstar_syn_syn_prefix "t_string"
        | FStar_Syntax_Syntax.Tm_fvar fv when
            let uu____1622 =
              FStar_Reflection_Data.fstar_refl_types_lid "binder"  in
            FStar_Syntax_Syntax.fv_eq_lid fv uu____1622 ->
            fstar_refl_data_prefix "t_binder"
        | FStar_Syntax_Syntax.Tm_fvar fv when
            let uu____1624 =
              FStar_Reflection_Data.fstar_refl_types_lid "term"  in
            FStar_Syntax_Syntax.fv_eq_lid fv uu____1624 ->
            fstar_refl_data_prefix "t_term"
        | FStar_Syntax_Syntax.Tm_fvar fv when
            let uu____1626 = FStar_Reflection_Data.fstar_refl_types_lid "fv"
               in
            FStar_Syntax_Syntax.fv_eq_lid fv uu____1626 ->
            fstar_refl_data_prefix "t_fv"
        | FStar_Syntax_Syntax.Tm_fvar fv when
            let uu____1628 =
              FStar_Reflection_Data.fstar_refl_syntax_lid "binder"  in
            FStar_Syntax_Syntax.fv_eq_lid fv uu____1628 ->
            fstar_refl_data_prefix "t_binders"
        | FStar_Syntax_Syntax.Tm_fvar fv when
            let uu____1630 =
              FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step"  in
            FStar_Syntax_Syntax.fv_eq_lid fv uu____1630 ->
            fstar_refl_data_prefix "t_norm_step"
        | FStar_Syntax_Syntax.Tm_app (h,args) ->
            let uu____1653 =
              let uu____1654 = FStar_Syntax_Subst.compress h  in
              uu____1654.FStar_Syntax_Syntax.n  in
            (match uu____1653 with
             | FStar_Syntax_Syntax.Tm_uinst (h',uu____1658) ->
                 let uu____1663 =
                   let uu____1664 = FStar_Syntax_Subst.compress h'  in
                   uu____1664.FStar_Syntax_Syntax.n  in
                 (match uu____1663 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.list_lid
                      ->
                      let arg_term =
                        let uu____1671 = FStar_List.hd args  in
                        FStar_Pervasives_Native.fst uu____1671  in
                      let uu____1686 =
                        let uu____1693 =
                          let uu____1694 = fstar_tc_common_prefix "t_list_of"
                             in
                          FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top uu____1694
                           in
                        let uu____1695 =
                          let uu____1698 =
                            let uu____1701 = mk_tac_param_type tcenv arg_term
                               in
                            [uu____1701]  in
                          FStar_List.map
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                            uu____1698
                           in
                        (uu____1693, uu____1695)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____1686
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.option_lid
                      ->
                      let arg_term =
                        let uu____1708 = FStar_List.hd args  in
                        FStar_Pervasives_Native.fst uu____1708  in
                      let uu____1723 =
                        let uu____1730 =
                          let uu____1731 =
                            fstar_tc_common_prefix "t_option_of"  in
                          FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top uu____1731
                           in
                        let uu____1732 =
                          let uu____1735 =
                            let uu____1738 = mk_tac_param_type tcenv arg_term
                               in
                            [uu____1738]  in
                          FStar_List.map
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.MLTY_Top)
                            uu____1735
                           in
                        (uu____1730, uu____1732)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____1723
                  | uu____1741 ->
                      let uu____1742 =
                        let uu____1747 =
                          let uu____1748 =
                            let uu____1749 = FStar_Syntax_Subst.compress h'
                               in
                            FStar_Syntax_Print.term_to_string uu____1749  in
                          Prims.strcat
                            "Type term not defined for higher-order type"
                            uu____1748
                           in
                        (FStar_Errors.Fatal_CallNotImplemented, uu____1747)
                         in
                      FStar_Errors.raise_err uu____1742)
             | uu____1750 ->
                 FStar_Errors.raise_err
                   (FStar_Errors.Fatal_CallNotImplemented, "Impossible\n"))
        | uu____1751 when Prims.op_Negation unrefined ->
            let t2 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant] tcenv t1
               in
            let uu____1753 = FStar_Syntax_Util.unrefine t2  in
            try_mk uu____1753 true
        | uu____1754 ->
            let uu____1755 =
              let uu____1760 =
                let uu____1761 =
                  let uu____1762 = FStar_Syntax_Subst.compress t1  in
                  FStar_Syntax_Print.term_to_string uu____1762  in
                Prims.strcat "Type term not defined for " uu____1761  in
              (FStar_Errors.Fatal_CallNotImplemented, uu____1760)  in
            FStar_Errors.raise_err uu____1755
         in
      try_mk t false
  
let (norm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun tcenv  ->
    fun t  ->
      let uu____1769 = FStar_Syntax_Util.unrefine t  in
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.UnfoldUntil
           FStar_Syntax_Syntax.Delta_constant] tcenv uu____1769
  
let mk_embedding_path :
  'Auu____1774 .
    'Auu____1774 ->
      emb_decl ->
        FStar_Syntax_Syntax.term ->
          FStar_Extraction_ML_Syntax.mlexpr' FStar_Pervasives_Native.option
  =
  fun tcenv  ->
    fun m  ->
      fun t  ->
        let nm =
          let uu____1792 =
            let uu____1793 = FStar_Syntax_Subst.compress t  in
            uu____1793.FStar_Syntax_Syntax.n  in
          match uu____1792 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
              FStar_Pervasives_Native.Some "int"
          | FStar_Syntax_Syntax.Tm_fvar fv when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
              FStar_Pervasives_Native.Some "bool"
          | FStar_Syntax_Syntax.Tm_fvar fv when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
              FStar_Pervasives_Native.Some "unit"
          | FStar_Syntax_Syntax.Tm_fvar fv when
              FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid
              -> FStar_Pervasives_Native.Some "string"
          | FStar_Syntax_Syntax.Tm_fvar fv when
              let uu____1803 =
                FStar_Reflection_Data.fstar_refl_types_lid "binder"  in
              FStar_Syntax_Syntax.fv_eq_lid fv uu____1803 ->
              FStar_Pervasives_Native.Some "binder"
          | FStar_Syntax_Syntax.Tm_fvar fv when
              let uu____1805 =
                FStar_Reflection_Data.fstar_refl_types_lid "term"  in
              FStar_Syntax_Syntax.fv_eq_lid fv uu____1805 ->
              FStar_Pervasives_Native.Some "term"
          | FStar_Syntax_Syntax.Tm_fvar fv when
              let uu____1807 =
                FStar_Reflection_Data.fstar_refl_types_lid "fv"  in
              FStar_Syntax_Syntax.fv_eq_lid fv uu____1807 ->
              FStar_Pervasives_Native.Some "fvar"
          | FStar_Syntax_Syntax.Tm_fvar fv when
              let uu____1809 =
                FStar_Reflection_Data.fstar_refl_syntax_lid "binders"  in
              FStar_Syntax_Syntax.fv_eq_lid fv uu____1809 ->
              FStar_Pervasives_Native.Some "binders"
          | FStar_Syntax_Syntax.Tm_fvar fv when
              let uu____1811 =
                FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step"  in
              FStar_Syntax_Syntax.fv_eq_lid fv uu____1811 ->
              FStar_Pervasives_Native.Some "norm_step"
          | uu____1812 -> FStar_Pervasives_Native.None  in
        FStar_Util.bind_opt nm
          (fun n1  ->
             let uu____1816 = mk_basic_embedding m n1  in
             FStar_Pervasives_Native.Some uu____1816)
  
let (must_mk_embedding_path :
  FStar_TypeChecker_Env.env ->
    emb_decl ->
      FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun tcenv  ->
    fun m  ->
      fun t  ->
        let uu____1826 =
          let uu____1829 = norm tcenv t  in
          mk_embedding_path tcenv m uu____1829  in
        match uu____1826 with
        | FStar_Pervasives_Native.Some m1 -> m1
        | FStar_Pervasives_Native.None  ->
            let uu____1831 =
              let uu____1836 =
                let uu____1837 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat "Embedding not defined for type " uu____1837  in
              (FStar_Errors.Fatal_CallNotImplemented, uu____1836)  in
            FStar_Errors.raise_err uu____1831
  
let rec (mk_tac_embedding_path :
  FStar_TypeChecker_Env.env ->
    emb_decl ->
      FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun tcenv  ->
    fun m  ->
      fun t  ->
        let t1 = norm tcenv t  in
        let uu____1848 = mk_embedding_path tcenv m t1  in
        match uu____1848 with
        | FStar_Pervasives_Native.Some mle -> mle
        | FStar_Pervasives_Native.None  ->
            let uu____1852 =
              let uu____1853 = FStar_Syntax_Subst.compress t1  in
              uu____1853.FStar_Syntax_Syntax.n  in
            (match uu____1852 with
             | FStar_Syntax_Syntax.Tm_app (h,args) ->
                 let uu____1878 =
                   let uu____1879 = FStar_Syntax_Subst.compress h  in
                   uu____1879.FStar_Syntax_Syntax.n  in
                 (match uu____1878 with
                  | FStar_Syntax_Syntax.Tm_uinst (h',uu____1883) ->
                      let uu____1888 =
                        let uu____1899 =
                          let uu____1900 = FStar_Syntax_Subst.compress h'  in
                          uu____1900.FStar_Syntax_Syntax.n  in
                        match uu____1899 with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.list_lid
                            ->
                            let arg_term =
                              let uu____1917 = FStar_List.hd args  in
                              FStar_Pervasives_Native.fst uu____1917  in
                            let uu____1932 =
                              let uu____1935 =
                                mk_tac_embedding_path tcenv m arg_term  in
                              [uu____1935]  in
                            let uu____1936 = mk_tac_param_type tcenv arg_term
                               in
                            ("list", uu____1932, uu____1936, false)
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.option_lid
                            ->
                            let arg_term =
                              let uu____1943 = FStar_List.hd args  in
                              FStar_Pervasives_Native.fst uu____1943  in
                            let uu____1958 =
                              let uu____1961 =
                                mk_tac_embedding_path tcenv m arg_term  in
                              [uu____1961]  in
                            let uu____1962 = mk_tac_param_type tcenv arg_term
                               in
                            ("option", uu____1958, uu____1962, false)
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.tactic_lid
                            ->
                            let arg_term =
                              let uu____1969 = FStar_List.hd args  in
                              FStar_Pervasives_Native.fst uu____1969  in
                            let uu____1984 =
                              let uu____1987 =
                                mk_tac_embedding_path tcenv m arg_term  in
                              [uu____1987]  in
                            let uu____1988 = mk_tac_param_type tcenv arg_term
                               in
                            ("list", uu____1984, uu____1988, true)
                        | uu____1991 ->
                            let uu____1992 =
                              let uu____1997 =
                                let uu____1998 =
                                  let uu____1999 =
                                    FStar_Syntax_Subst.compress h'  in
                                  FStar_Syntax_Print.term_to_string
                                    uu____1999
                                   in
                                Prims.strcat
                                  "Embedding not defined for higher-order type "
                                  uu____1998
                                 in
                              (FStar_Errors.Fatal_CallNotImplemented,
                                uu____1997)
                               in
                            FStar_Errors.raise_err uu____1992
                         in
                      (match uu____1888 with
                       | (ht,hargs,type_arg,is_tactic) ->
                           let hargs1 =
                             match m with
                             | Embed  -> FStar_List.append hargs [type_arg]
                             | Unembed  -> hargs  in
                           if is_tactic
                           then
                             (match m with
                              | Embed  ->
                                  FStar_Errors.raise_err
                                    (FStar_Errors.Fatal_CallNotImplemented,
                                      "Embedding not defined for tactic type\n")
                              | Unembed  -> mk_tactic_unembedding hargs1)
                           else
                             (let uu____2024 =
                                let uu____2031 =
                                  let uu____2032 = mk_basic_embedding m ht
                                     in
                                  FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top
                                    uu____2032
                                   in
                                let uu____2033 =
                                  FStar_List.map
                                    (FStar_Extraction_ML_Syntax.with_ty
                                       FStar_Extraction_ML_Syntax.MLTY_Top)
                                    hargs1
                                   in
                                (uu____2031, uu____2033)  in
                              FStar_Extraction_ML_Syntax.MLE_App uu____2024))
                  | uu____2038 ->
                      FStar_Errors.raise_err
                        (FStar_Errors.Fatal_CallNotImplemented,
                          "Impossible\n"))
             | uu____2039 ->
                 let uu____2040 =
                   let uu____2045 =
                     let uu____2046 = FStar_Syntax_Print.term_to_string t1
                        in
                     Prims.strcat "Embedding not defined for type "
                       uu____2046
                      in
                   (FStar_Errors.Fatal_CallNotImplemented, uu____2045)  in
                 FStar_Errors.raise_err uu____2040)
  
let (interpret_plugin_as_term_fun :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mlexpr' ->
          (FStar_Extraction_ML_Syntax.mlexpr',Prims.nat,Prims.bool)
            FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun tcenv  ->
    fun fv  ->
      fun fv_t  ->
        fun ml_fv  ->
          let w =
            FStar_Extraction_ML_Syntax.with_ty
              FStar_Extraction_ML_Syntax.MLTY_Top
             in
          let mk_lam nm e =
            let psc = str_to_name nm  in
            FStar_Extraction_ML_Syntax.MLE_Fun
              ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], (w e))
             in
          try
            let uu____2122 = FStar_Syntax_Util.arrow_formals_comp fv_t  in
            match uu____2122 with
            | (bs,c) ->
                let arg_types =
                  FStar_List.map
                    (fun x  ->
                       (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
                    bs
                   in
                let arity = FStar_List.length bs  in
                let result_typ = FStar_Syntax_Util.comp_result c  in
                let uu____2180 = FStar_Syntax_Util.is_pure_comp c  in
                if uu____2180
                then
                  let embed_fun_N =
                    let uu____2190 =
                      let uu____2191 =
                        let uu____2192 = FStar_Util.string_of_int arity  in
                        Prims.strcat "arrow_" uu____2192  in
                      mk_basic_embedding Embed uu____2191  in
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top) uu____2190
                     in
                  let un_embeddings =
                    FStar_List.map
                      (fun x  ->
                         let uu____2205 =
                           must_mk_embedding_path tcenv Unembed x  in
                         w uu____2205) arg_types
                     in
                  let embed_res =
                    must_mk_embedding_path tcenv Embed result_typ  in
                  let args =
                    let uu____2210 =
                      let uu____2213 =
                        let uu____2216 = lid_to_top_name fv  in [uu____2216]
                         in
                      (w embed_res) :: uu____2213  in
                    FStar_List.append un_embeddings uu____2210  in
                  let uu____2217 =
                    let uu____2224 =
                      FStar_All.pipe_left (mk_lam "_")
                        (FStar_Extraction_ML_Syntax.MLE_App
                           (embed_fun_N, args))
                       in
                    (uu____2224, arity, true)  in
                  FStar_Pervasives_Native.Some uu____2217
                else
                  (let uu____2238 =
                     let uu____2239 =
                       FStar_TypeChecker_Env.norm_eff_name tcenv
                         (FStar_Syntax_Util.comp_effect_name c)
                        in
                     FStar_Ident.lid_equals uu____2239
                       FStar_Parser_Const.tac_effect_lid
                      in
                   if uu____2238
                   then
                     let h =
                       let uu____2249 =
                         let uu____2250 = FStar_Util.string_of_int arity  in
                         Prims.strcat
                           "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                           uu____2250
                          in
                       str_to_top_name uu____2249  in
                     let tac_fun =
                       let uu____2258 =
                         let uu____2265 =
                           let uu____2266 =
                             let uu____2267 = FStar_Util.string_of_int arity
                                in
                             Prims.strcat "FStar_Tactics_Native.from_tactic_"
                               uu____2267
                              in
                           str_to_top_name uu____2266  in
                         let uu____2274 =
                           let uu____2277 = lid_to_top_name fv  in
                           [uu____2277]  in
                         (uu____2265, uu____2274)  in
                       FStar_Extraction_ML_Syntax.MLE_App uu____2258  in
                     let tac_lid_app =
                       let uu____2281 =
                         let uu____2288 =
                           str_to_top_name "FStar_Ident.lid_of_str"  in
                         (uu____2288, [w ml_fv])  in
                       FStar_Extraction_ML_Syntax.MLE_App uu____2281  in
                     let psc = str_to_name "psc"  in
                     let args =
                       let uu____2295 =
                         let uu____2298 =
                           FStar_List.map
                             (mk_tac_embedding_path tcenv Unembed) arg_types
                            in
                         let uu____2301 =
                           let uu____2304 =
                             mk_tac_embedding_path tcenv Embed result_typ  in
                           let uu____2305 =
                             let uu____2308 =
                               mk_tac_param_type tcenv result_typ  in
                             let uu____2309 =
                               let uu____2312 =
                                 let uu____2315 =
                                   let uu____2318 = str_to_name "args"  in
                                   [uu____2318]  in
                                 psc :: uu____2315  in
                               tac_lid_app :: uu____2312  in
                             uu____2308 :: uu____2309  in
                           uu____2304 :: uu____2305  in
                         FStar_List.append uu____2298 uu____2301  in
                       FStar_List.append
                         [FStar_Extraction_ML_Syntax.MLE_Const
                            (FStar_Extraction_ML_Syntax.MLC_Bool true);
                         tac_fun] uu____2295
                        in
                     let uu____2319 =
                       let uu____2326 =
                         let uu____2327 =
                           let uu____2328 =
                             let uu____2329 =
                               let uu____2336 = FStar_List.map w args  in
                               (h, uu____2336)  in
                             FStar_Extraction_ML_Syntax.MLE_App uu____2329
                              in
                           FStar_All.pipe_left (mk_lam "args") uu____2328  in
                         FStar_All.pipe_left (mk_lam "psc") uu____2327  in
                       (uu____2326, arity, false)  in
                     FStar_Pervasives_Native.Some uu____2319
                   else
                     (let uu____2352 =
                        let uu____2357 =
                          let uu____2358 =
                            FStar_Syntax_Print.term_to_string fv_t  in
                          Prims.strcat "Plugins not defined for type "
                            uu____2358
                           in
                        (FStar_Errors.Fatal_CallNotImplemented, uu____2357)
                         in
                      FStar_Errors.raise_err uu____2352))
          with
          | FStar_Errors.Error
              (FStar_Errors.Fatal_CallNotImplemented ,msg,uu____2381) ->
              ((let uu____2383 = FStar_Ident.string_of_lid fv  in
                not_implemented_warning fv_t.FStar_Syntax_Syntax.pos
                  uu____2383 msg);
               FStar_Pervasives_Native.None)
  