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
  (FStar_Extraction_ML_Syntax.mlidents,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____313 = try_subst ts args  in
      match uu____313 with
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
    fun uu___59_324  ->
      match uu___59_324 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____333 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____333 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____339 = try_subst ts args  in
               (match uu____339 with
                | FStar_Pervasives_Native.None  ->
                    let uu____344 =
                      let uu____345 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____346 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____347 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____345 uu____346 uu____347
                       in
                    failwith uu____344
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____351 -> FStar_Pervasives_Native.None)
      | uu____354 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____361) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____362 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___60_369  ->
    match uu___60_369 with
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
        | uu____379 ->
            let uu____384 =
              let uu____385 = FStar_Range.string_of_range r  in
              let uu____386 = eff_to_string f  in
              let uu____387 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____385
                uu____386 uu____387
               in
            failwith uu____384
  
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
    (fun uu____416  ->
       fun t  ->
         match uu____416 with
         | (uu____422,t0) ->
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
                | uu____509 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____541 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____548 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____548 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____558;
                     FStar_Extraction_ML_Syntax.loc = uu____559;_}
                   ->
                   let uu____580 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____580
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____596 = type_leq unfold_ty t2 t2'  in
                        (if uu____596
                         then
                           let body1 =
                             let uu____607 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____607
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____612 =
                             let uu____615 =
                               let uu____616 =
                                 let uu____619 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____619
                                  in
                               FStar_All.pipe_left uu____616
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____615  in
                           (true, uu____612)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____648 =
                           let uu____655 =
                             let uu____658 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_43  ->
                                  FStar_Pervasives_Native.Some _0_43)
                               uu____658
                              in
                           type_leq_c unfold_ty uu____655 t2 t2'  in
                         match uu____648 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____682 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____682
                               | uu____691 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____699 ->
                   let uu____702 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____702
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____738 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____738
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____754 = unfold_ty t  in
                 match uu____754 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____768 = unfold_ty t'  in
                     (match uu____768 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____790 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____790
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____807,uu____808) ->
              let uu____815 = unfold_ty t  in
              (match uu____815 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____829 -> (false, FStar_Pervasives_Native.None))
          | (uu____834,FStar_Extraction_ML_Syntax.MLTY_Named uu____835) ->
              let uu____842 = unfold_ty t'  in
              (match uu____842 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____856 -> (false, FStar_Pervasives_Native.None))
          | uu____861 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____872 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____872 FStar_Pervasives_Native.fst

let is_type_abstraction :
  'a 'b 'c .
    (('a,'b) FStar_Util.either,'c) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.bool
  =
  fun uu___61_910  ->
    match uu___61_910 with
    | (FStar_Util.Inl uu____921,uu____922)::uu____923 -> true
    | uu____946 -> false
  
let (is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____967  ->
    match uu____967 with
    | (ns,n1) ->
        let uu____982 =
          let uu____983 = FStar_Util.concat_l "." (FStar_List.append ns [n1])
             in
          FStar_Parser_Const.is_tuple_datacon_string uu____983  in
        if uu____982
        then
          let uu____986 =
            let uu____987 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____987  in
          FStar_Pervasives_Native.Some uu____986
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____998 = is_xtuple mlp  in
        (match uu____998 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1002 -> e)
    | uu____1005 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___62_1012  ->
    match uu___62_1012 with
    | f::uu____1018 ->
        let uu____1021 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1021 with
         | (ns,uu____1031) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1042 -> failwith "impos"
  
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
  fun uu____1091  ->
    match uu____1091 with
    | (ns,n1) ->
        let uu____1106 =
          let uu____1107 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1107  in
        if uu____1106
        then
          let uu____1110 =
            let uu____1111 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1111  in
          FStar_Pervasives_Native.Some uu____1110
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1122 = is_xtuple_ty mlp  in
        (match uu____1122 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1126 -> t)
    | uu____1129 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1137 = codegen_fsharp ()  in
    if uu____1137
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1147  ->
    match uu____1147 with
    | (ns,n1) ->
        let uu____1160 = codegen_fsharp ()  in
        if uu____1160
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____1171 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1171, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1191 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1191
      then true
      else
        (let uu____1193 = unfold_ty t  in
         match uu____1193 with
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
            let uu____1213 =
              let uu____1220 = eraseTypeDeep unfold_ty tyd  in
              let uu____1224 = eraseTypeDeep unfold_ty tycd  in
              (uu____1220, etag, uu____1224)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1213
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1235 = erasableType unfold_ty t  in
          if uu____1235
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1240 =
               let uu____1247 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1247, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1240)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1258 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1258
      | uu____1264 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1267 =
    let uu____1270 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1270  in
  FStar_All.pipe_left uu____1267
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
          let uu____1335 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1335
  
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1345 = FStar_Range.file_of_range r  in (line, uu____1345)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1362,b) ->
        let uu____1364 = doms_and_cod b  in
        (match uu____1364 with | (ds,c) -> ((a :: ds), c))
    | uu____1385 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1395 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1395
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1420,b) ->
        let uu____1422 = uncurry_mlty_fun b  in
        (match uu____1422 with | (args,res) -> ((a :: args), res))
    | uu____1443 -> ([], t)
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> Prims.unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1455 =
          let uu____1460 =
            FStar_Util.format2
              ". Tactic %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1460)  in
        FStar_Errors.log_issue r uu____1455
  
type emb_decl =
  | Embed 
  | Unembed [@@deriving show]
let (uu___is_Embed : emb_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____1464 -> false
  
let (uu___is_Unembed : emb_decl -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____1468 -> false
  
type embedding =
  {
  embed: FStar_Extraction_ML_Syntax.mlexpr ;
  unembed: FStar_Extraction_ML_Syntax.mlexpr ;
  type_repr: FStar_Extraction_ML_Syntax.mlexpr }[@@deriving show]
let (__proj__Mkembedding__item__embed :
  embedding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee  ->
    match projectee with
    | { embed = __fname__embed; unembed = __fname__unembed;
        type_repr = __fname__type_repr;_} -> __fname__embed
  
let (__proj__Mkembedding__item__unembed :
  embedding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee  ->
    match projectee with
    | { embed = __fname__embed; unembed = __fname__unembed;
        type_repr = __fname__type_repr;_} -> __fname__unembed
  
let (__proj__Mkembedding__item__type_repr :
  embedding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee  ->
    match projectee with
    | { embed = __fname__embed; unembed = __fname__unembed;
        type_repr = __fname__type_repr;_} -> __fname__type_repr
  
type variance =
  | Covariant 
  | Contravariant 
  | Invariant [@@deriving show]
let (uu___is_Covariant : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | Covariant  -> true | uu____1502 -> false
  
let (uu___is_Contravariant : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | Contravariant  -> true | uu____1506 -> false
  
let (uu___is_Invariant : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | Invariant  -> true | uu____1510 -> false
  
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
              [FStar_TypeChecker_Normalize.Beta;
              FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.AllowUnboundUniverses] tcenv t
             in
          let w =
            FStar_Extraction_ML_Syntax.with_ty
              FStar_Extraction_ML_Syntax.MLTY_Top
             in
          let lid_to_name l =
            let uu____1539 =
              let uu____1540 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1540  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1539
             in
          let lid_to_top_name l =
            let uu____1545 =
              let uu____1546 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1546  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1545
             in
          let str_to_name s =
            let uu____1551 = FStar_Ident.lid_of_str s  in
            lid_to_name uu____1551  in
          let str_to_top_name s =
            let uu____1556 = FStar_Ident.lid_of_str s  in
            lid_to_top_name uu____1556  in
          let fstar_syn_syn_prefix s =
            str_to_name (Prims.strcat "FStar_Syntax_Syntax." s)  in
          let fstar_tc_common_prefix s =
            str_to_name (Prims.strcat "FStar_TypeChecker_Common." s)  in
          let fstar_refl_basic_prefix s =
            str_to_name (Prims.strcat "FStar_Reflection_Basic." s)  in
          let fstar_refl_data_prefix s =
            str_to_name (Prims.strcat "FStar_Reflection_Data." s)  in
          let fstar_emb_basic_prefix s =
            str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)  in
          let mk_basic_embedding m s =
            match m with
            | Embed  -> fstar_emb_basic_prefix (Prims.strcat "embed_" s)
            | Unembed  -> fstar_emb_basic_prefix (Prims.strcat "unembed_" s)
             in
          let mk_lam nm e =
            FStar_All.pipe_left w
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
             in
          let id_embedding nm =
            let id1 =
              let uu____1610 = str_to_name "x"  in mk_lam "x" uu____1610  in
            let uu____1611 = str_to_name nm  in
            { embed = id1; unembed = id1; type_repr = uu____1611 }  in
          let known_type_constructors =
            let uu____1623 =
              let uu____1632 = fstar_syn_syn_prefix "t_int"  in
              (FStar_Parser_Const.int_lid, [], uu____1632)  in
            let uu____1635 =
              let uu____1646 =
                let uu____1655 = fstar_syn_syn_prefix "t_bool"  in
                (FStar_Parser_Const.bool_lid, [], uu____1655)  in
              let uu____1658 =
                let uu____1669 =
                  let uu____1678 = fstar_syn_syn_prefix "t_unit"  in
                  (FStar_Parser_Const.unit_lid, [], uu____1678)  in
                let uu____1681 =
                  let uu____1692 =
                    let uu____1701 = fstar_syn_syn_prefix "t_string"  in
                    (FStar_Parser_Const.string_lid, [], uu____1701)  in
                  let uu____1704 =
                    let uu____1715 =
                      let uu____1724 =
                        FStar_Reflection_Data.fstar_refl_types_lid "term"  in
                      let uu____1725 = fstar_refl_data_prefix "t_term"  in
                      (uu____1724, [], uu____1725)  in
                    let uu____1728 =
                      let uu____1739 =
                        let uu____1748 =
                          FStar_Reflection_Data.fstar_refl_types_lid "fv"  in
                        let uu____1749 = fstar_refl_data_prefix "t_fv"  in
                        (uu____1748, [], uu____1749)  in
                      let uu____1752 =
                        let uu____1763 =
                          let uu____1772 =
                            FStar_Reflection_Data.fstar_refl_types_lid
                              "binder"
                             in
                          let uu____1773 = fstar_refl_data_prefix "t_binder"
                             in
                          (uu____1772, [], uu____1773)  in
                        let uu____1776 =
                          let uu____1787 =
                            let uu____1796 =
                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                "binders"
                               in
                            let uu____1797 =
                              fstar_refl_data_prefix "t_binders"  in
                            (uu____1796, [], uu____1797)  in
                          let uu____1800 =
                            let uu____1811 =
                              let uu____1820 =
                                FStar_Reflection_Data.fstar_refl_syntax_lid
                                  "norm_step"
                                 in
                              let uu____1821 =
                                fstar_refl_data_prefix "t_norm_step"  in
                              (uu____1820, [], uu____1821)  in
                            let uu____1824 =
                              let uu____1835 =
                                let uu____1844 =
                                  fstar_tc_common_prefix "t_list_of"  in
                                (FStar_Parser_Const.list_lid, [Covariant],
                                  uu____1844)
                                 in
                              let uu____1847 =
                                let uu____1858 =
                                  let uu____1867 =
                                    fstar_tc_common_prefix "t_option_of"  in
                                  (FStar_Parser_Const.option_lid,
                                    [Covariant], uu____1867)
                                   in
                                let uu____1870 =
                                  let uu____1881 =
                                    let uu____1890 =
                                      FStar_Parser_Const.mk_tuple_lid
                                        (Prims.parse_int "2")
                                        FStar_Range.dummyRange
                                       in
                                    let uu____1891 =
                                      fstar_tc_common_prefix "t_tuple2_of"
                                       in
                                    (uu____1890, [Covariant; Covariant],
                                      uu____1891)
                                     in
                                  [uu____1881]  in
                                uu____1858 :: uu____1870  in
                              uu____1835 :: uu____1847  in
                            uu____1811 :: uu____1824  in
                          uu____1787 :: uu____1800  in
                        uu____1763 :: uu____1776  in
                      uu____1739 :: uu____1752  in
                    uu____1715 :: uu____1728  in
                  uu____1692 :: uu____1704  in
                uu____1669 :: uu____1681  in
              uu____1646 :: uu____1658  in
            uu____1623 :: uu____1635  in
          let is_known_type_constructor fv1 n1 =
            FStar_Util.for_some
              (fun uu____2021  ->
                 match uu____2021 with
                 | (x,args,uu____2032) ->
                     (FStar_Syntax_Syntax.fv_eq_lid fv1 x) &&
                       (n1 = (FStar_List.length args)))
              known_type_constructors
             in
          let embed_type_app fv1 arg_embeddings =
            let nm =
              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
               in
            let uu____2053 =
              let uu____2062 =
                FStar_Util.find_opt
                  (fun uu____2085  ->
                     match uu____2085 with
                     | (x,uu____2095,uu____2096) ->
                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                  known_type_constructors
                 in
              FStar_All.pipe_right uu____2062 FStar_Util.must  in
            match uu____2053 with
            | (uu____2127,variances,trepr_head) ->
                let choose1 e_or_u variance embedding =
                  let term_embedding =
                    match variance with
                    | Covariant  ->
                        (match e_or_u with
                         | Embed  -> [embedding.embed]
                         | Unembed  -> [embedding.unembed])
                    | Contravariant  ->
                        (match e_or_u with
                         | Embed  -> [embedding.unembed]
                         | Unembed  -> [embedding.embed])
                    | Invariant  -> [embedding.embed; embedding.unembed]  in
                  FStar_List.append term_embedding [embedding.type_repr]  in
                let mk1 embed_or_unembed =
                  let head1 = mk_basic_embedding embed_or_unembed nm  in
                  match variances with
                  | [] -> head1
                  | uu____2160 ->
                      let args =
                        FStar_List.map2 (choose1 embed_or_unembed) variances
                          arg_embeddings
                         in
                      FStar_All.pipe_left w
                        (FStar_Extraction_ML_Syntax.MLE_App
                           (head1, (FStar_List.flatten args)))
                   in
                let type_repr =
                  match variances with
                  | [] -> trepr_head
                  | uu____2173 ->
                      let uu____2176 =
                        let uu____2177 =
                          let uu____2184 =
                            FStar_List.map (fun x  -> x.type_repr)
                              arg_embeddings
                             in
                          (trepr_head, uu____2184)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____2177  in
                      FStar_All.pipe_left w uu____2176
                   in
                let uu____2191 = mk1 Embed  in
                let uu____2192 = mk1 Unembed  in
                { embed = uu____2191; unembed = uu____2192; type_repr }
             in
          let find_env_entry bv uu____2203 =
            match uu____2203 with
            | (bv',uu____2209) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
          let rec mk_embedding env t2 =
            let uu____2229 =
              let uu____2230 = FStar_Syntax_Subst.compress t2  in
              uu____2230.FStar_Syntax_Syntax.n  in
            match uu____2229 with
            | FStar_Syntax_Syntax.Tm_name bv when
                FStar_Util.for_some (find_env_entry bv) env ->
                let uu____2238 =
                  let uu____2243 =
                    FStar_Util.find_opt (find_env_entry bv) env  in
                  FStar_Util.must uu____2243  in
                FStar_Pervasives_Native.snd uu____2238
            | uu____2258 ->
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
                let uu____2260 = FStar_Syntax_Util.head_and_args t3  in
                (match uu____2260 with
                 | (head1,args) ->
                     let n_args = FStar_List.length args  in
                     let uu____2304 =
                       let uu____2305 = FStar_Syntax_Util.un_uinst head1  in
                       uu____2305.FStar_Syntax_Syntax.n  in
                     (match uu____2304 with
                      | FStar_Syntax_Syntax.Tm_refine (b,uu____2309) ->
                          mk_embedding env b.FStar_Syntax_Syntax.sort
                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                          is_known_type_constructor fv1 n_args ->
                          let arg_embeddings =
                            FStar_List.map
                              (fun uu____2329  ->
                                 match uu____2329 with
                                 | (t4,uu____2335) -> mk_embedding env t4)
                              args
                             in
                          embed_type_app fv1 arg_embeddings
                      | uu____2336 ->
                          let uu____2337 =
                            let uu____2342 =
                              let uu____2343 =
                                FStar_Syntax_Print.term_to_string t3  in
                              Prims.strcat "Embedding not defined for type "
                                uu____2343
                               in
                            (FStar_Errors.Fatal_CallNotImplemented,
                              uu____2342)
                             in
                          FStar_Errors.raise_err uu____2337))
             in
          let uu____2344 = FStar_Syntax_Util.arrow_formals_comp t1  in
          match uu____2344 with
          | (bs,c) ->
              let arity = FStar_List.length bs  in
              let result_typ = FStar_Syntax_Util.comp_result c  in
              let uu____2385 =
                let uu____2402 =
                  FStar_Util.prefix_until
                    (fun uu____2436  ->
                       match uu____2436 with
                       | (b,uu____2442) ->
                           let uu____2443 =
                             let uu____2444 =
                               FStar_Syntax_Subst.compress
                                 b.FStar_Syntax_Syntax.sort
                                in
                             uu____2444.FStar_Syntax_Syntax.n  in
                           (match uu____2443 with
                            | FStar_Syntax_Syntax.Tm_type uu____2447 -> false
                            | uu____2448 -> true)) bs
                   in
                match uu____2402 with
                | FStar_Pervasives_Native.None  -> (bs, [])
                | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                    (tvars, (x :: rest))
                 in
              (match uu____2385 with
               | (type_vars,bs1) ->
                   let tvar_names =
                     FStar_List.mapi
                       (fun i  ->
                          fun tv  ->
                            let uu____2626 = FStar_Util.string_of_int i  in
                            Prims.strcat "tv_" uu____2626) type_vars
                      in
                   let tvar_context =
                     FStar_List.map2
                       (fun b  ->
                          fun nm  ->
                            let uu____2651 = id_embedding nm  in
                            ((FStar_Pervasives_Native.fst b), uu____2651))
                       type_vars tvar_names
                      in
                   let rec aux accum_embeddings env bs2 =
                     match bs2 with
                     | [] ->
                         let arg_unembeddings =
                           FStar_All.pipe_right
                             (FStar_List.rev accum_embeddings)
                             (FStar_List.map (fun x  -> x.unembed))
                            in
                         let res_embedding = mk_embedding env result_typ  in
                         let uu____2720 = FStar_Syntax_Util.is_pure_comp c
                            in
                         if uu____2720
                         then
                           let embed_fun_N =
                             let uu____2730 =
                               let uu____2731 =
                                 FStar_Util.string_of_int arity  in
                               Prims.strcat "arrow_" uu____2731  in
                             mk_basic_embedding Embed uu____2730  in
                           let args =
                             let uu____2741 =
                               let uu____2744 =
                                 let uu____2747 = lid_to_top_name fv  in
                                 [uu____2747]  in
                               (res_embedding.embed) :: uu____2744  in
                             FStar_List.append arg_unembeddings uu____2741
                              in
                           let fun_embedding =
                             FStar_All.pipe_left w
                               (FStar_Extraction_ML_Syntax.MLE_App
                                  (embed_fun_N, args))
                              in
                           let tabs =
                             FStar_List.fold_right mk_lam tvar_names
                               fun_embedding
                              in
                           let uu____2752 =
                             let uu____2759 = mk_lam "_psc" tabs  in
                             (uu____2759, arity, true)  in
                           FStar_Pervasives_Native.Some uu____2752
                         else
                           (let uu____2771 =
                              let uu____2772 =
                                FStar_TypeChecker_Env.norm_eff_name tcenv
                                  (FStar_Syntax_Util.comp_effect_name c)
                                 in
                              FStar_Ident.lid_equals uu____2772
                                FStar_Parser_Const.tac_effect_lid
                               in
                            if uu____2771
                            then
                              let h =
                                let uu____2782 =
                                  let uu____2783 =
                                    FStar_Util.string_of_int arity  in
                                  Prims.strcat
                                    "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                                    uu____2783
                                   in
                                str_to_top_name uu____2782  in
                              let tac_fun =
                                let uu____2791 =
                                  let uu____2792 =
                                    let uu____2799 =
                                      let uu____2800 =
                                        let uu____2801 =
                                          FStar_Util.string_of_int arity  in
                                        Prims.strcat
                                          "FStar_Tactics_Native.from_tactic_"
                                          uu____2801
                                         in
                                      str_to_top_name uu____2800  in
                                    let uu____2808 =
                                      let uu____2811 = lid_to_top_name fv  in
                                      [uu____2811]  in
                                    (uu____2799, uu____2808)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____2792
                                   in
                                FStar_All.pipe_left w uu____2791  in
                              let tac_lid_app =
                                let uu____2815 =
                                  let uu____2816 =
                                    let uu____2823 =
                                      str_to_top_name
                                        "FStar_Ident.lid_of_str"
                                       in
                                    (uu____2823, [w ml_fv])  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____2816
                                   in
                                FStar_All.pipe_left w uu____2815  in
                              let psc = str_to_name "psc"  in
                              let args = str_to_name "args"  in
                              let args1 =
                                let uu____2831 =
                                  let uu____2834 =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_Bool
                                            true))
                                     in
                                  [uu____2834; tac_fun]  in
                                FStar_List.append uu____2831
                                  (FStar_List.append arg_unembeddings
                                     [res_embedding.embed;
                                     res_embedding.type_repr;
                                     tac_lid_app;
                                     psc;
                                     args])
                                 in
                              let uu____2835 =
                                let uu____2842 =
                                  let uu____2843 =
                                    let uu____2844 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h, args1))
                                       in
                                    mk_lam "args" uu____2844  in
                                  FStar_All.pipe_left (mk_lam "psc")
                                    uu____2843
                                   in
                                (uu____2842, arity, false)  in
                              FStar_Pervasives_Native.Some uu____2835
                            else
                              (let uu____2858 =
                                 let uu____2863 =
                                   let uu____2864 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   Prims.strcat
                                     "Plugins not defined for type "
                                     uu____2864
                                    in
                                 (FStar_Errors.Fatal_CallNotImplemented,
                                   uu____2863)
                                  in
                               FStar_Errors.raise_err uu____2858))
                     | (b,uu____2874)::bs3 ->
                         let uu____2886 =
                           let uu____2889 =
                             mk_embedding env b.FStar_Syntax_Syntax.sort  in
                           uu____2889 :: accum_embeddings  in
                         aux uu____2886 env bs3
                      in
                   aux [] tvar_context bs1)
  