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
      try (fun uu___265_103  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___264_106 ->
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
          let uu____278 =
            let uu____285 = FStar_List.map (subst_aux subst1) args  in
            (uu____285, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____278
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____293 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____293
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____308  ->
    fun args  ->
      match uu____308 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____319 =
               let uu____320 = FStar_List.zip formals args  in
               subst_aux uu____320 t  in
             FStar_Pervasives_Native.Some uu____319)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____349 = try_subst ts args  in
      match uu____349 with
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
    fun uu___260_364  ->
      match uu___260_364 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____373 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____373 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____379 = try_subst ts args  in
               (match uu____379 with
                | FStar_Pervasives_Native.None  ->
                    let uu____384 =
                      let uu____385 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____386 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____387 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____385 uu____386 uu____387
                       in
                    failwith uu____384
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____391 -> FStar_Pervasives_Native.None)
      | uu____394 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____405) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____406 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___261_415  ->
    match uu___261_415 with
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
        | uu____431 ->
            let uu____436 =
              let uu____437 = FStar_Range.string_of_range r  in
              let uu____438 = eff_to_string f  in
              let uu____439 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____437
                uu____438 uu____439
               in
            failwith uu____436
  
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
    (fun uu____476  ->
       fun t  ->
         match uu____476 with
         | (uu____482,t0) ->
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
                | uu____591 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____623 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____630 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____630 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____640;
                     FStar_Extraction_ML_Syntax.loc = uu____641;_}
                   ->
                   let uu____662 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____662
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____678 = type_leq unfold_ty t2 t2'  in
                        (if uu____678
                         then
                           let body1 =
                             let uu____689 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____689
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____694 =
                             let uu____697 =
                               let uu____698 =
                                 let uu____703 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____703
                                  in
                               FStar_All.pipe_left uu____698
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____697  in
                           (true, uu____694)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____732 =
                           let uu____739 =
                             let uu____742 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_19  ->
                                  FStar_Pervasives_Native.Some _0_19)
                               uu____742
                              in
                           type_leq_c unfold_ty uu____739 t2 t2'  in
                         match uu____732 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____766 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____766
                               | uu____775 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____783 ->
                   let uu____786 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____786
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____822 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____822
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____838 = unfold_ty t  in
                 match uu____838 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____852 = unfold_ty t'  in
                     (match uu____852 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____874 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____874
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____891,uu____892) ->
              let uu____899 = unfold_ty t  in
              (match uu____899 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____913 -> (false, FStar_Pervasives_Native.None))
          | (uu____918,FStar_Extraction_ML_Syntax.MLTY_Named uu____919) ->
              let uu____926 = unfold_ty t'  in
              (match uu____926 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____940 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____947 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____959 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____959 FStar_Pervasives_Native.fst

let is_type_abstraction :
  'a 'b 'c .
    (('a,'b) FStar_Util.either,'c) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.bool
  =
  fun uu___262_1002  ->
    match uu___262_1002 with
    | (FStar_Util.Inl uu____1013,uu____1014)::uu____1015 -> true
    | uu____1038 -> false
  
let (is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1061  ->
    match uu____1061 with
    | (ns,n1) ->
        let uu____1076 =
          let uu____1077 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____1077  in
        if uu____1076
        then
          let uu____1080 =
            let uu____1081 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____1081  in
          FStar_Pervasives_Native.Some uu____1080
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1095 = is_xtuple mlp  in
        (match uu____1095 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1099 -> e)
    | uu____1102 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___263_1111  ->
    match uu___263_1111 with
    | f::uu____1117 ->
        let uu____1120 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1120 with
         | (ns,uu____1130) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1141 -> failwith "impos"
  
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
  fun uu____1197  ->
    match uu____1197 with
    | (ns,n1) ->
        let uu____1212 =
          let uu____1213 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1213  in
        if uu____1212
        then
          let uu____1216 =
            let uu____1217 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1217  in
          FStar_Pervasives_Native.Some uu____1216
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1231 = is_xtuple_ty mlp  in
        (match uu____1231 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1235 -> t)
    | uu____1238 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1248 = codegen_fsharp ()  in
    if uu____1248
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1260  ->
    match uu____1260 with
    | (ns,n1) ->
        let uu____1273 = codegen_fsharp ()  in
        if uu____1273
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____1286 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1286, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1312 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1312
      then true
      else
        (let uu____1314 = unfold_ty t  in
         match uu____1314 with
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
            let uu____1340 =
              let uu____1347 = eraseTypeDeep unfold_ty tyd  in
              let uu____1351 = eraseTypeDeep unfold_ty tycd  in
              (uu____1347, etag, uu____1351)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1340
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1362 = erasableType unfold_ty t  in
          if uu____1362
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1367 =
               let uu____1374 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1374, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1367)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1385 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1385
      | uu____1391 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1394 =
    let uu____1399 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1399  in
  FStar_All.pipe_left uu____1394
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
          let uu____1472 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1472
  
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1484 = FStar_Range.file_of_range r  in (line, uu____1484)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1503,b) ->
        let uu____1505 = doms_and_cod b  in
        (match uu____1505 with | (ds,c) -> ((a :: ds), c))
    | uu____1526 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1538 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1538
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1565,b) ->
        let uu____1567 = uncurry_mlty_fun b  in
        (match uu____1567 with | (args,res) -> ((a :: args), res))
    | uu____1588 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____1600 -> true
    | uu____1601 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____1608 -> uu____1608
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1624 =
          let uu____1629 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1629)  in
        FStar_Errors.log_issue r uu____1624
  
type emb_loc =
  | S 
  | R 
let (uu___is_S : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | S  -> true | uu____1635 -> false 
let (uu___is_R : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | R  -> true | uu____1641 -> false 
let (interpret_plugin_as_term_fun :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ ->
        Prims.int FStar_Pervasives_Native.option ->
          FStar_Extraction_ML_Syntax.mlexpr' ->
            (FStar_Extraction_ML_Syntax.mlexpr,Prims.int,Prims.bool)
              FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
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
              let uu____1692 =
                let uu____1693 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____1693  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1692
               in
            let lid_to_top_name l =
              let uu____1700 =
                let uu____1701 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____1701  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1700
               in
            let str_to_name s =
              let uu____1708 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____1708  in
            let str_to_top_name s =
              let uu____1715 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____1715  in
            let fstar_syn_emb_prefix s =
              str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)  in
            let fstar_refl_emb_prefix s =
              str_to_name (Prims.strcat "FStar_Reflection_Embeddings." s)  in
            let fv_lid_embedded =
              let uu____1729 =
                let uu____1730 =
                  let uu____1737 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____1738 =
                    let uu____1741 =
                      let uu____1742 =
                        let uu____1743 =
                          let uu____1744 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____1744
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____1743  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1742
                       in
                    [uu____1741]  in
                  (uu____1737, uu____1738)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____1730  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1729
               in
            let mk_basic_embedding l s =
              let emb_prefix =
                match l with
                | S  -> fstar_syn_emb_prefix
                | R  -> fstar_refl_emb_prefix  in
              emb_prefix (Prims.strcat "e_" s)  in
            let mk_arrow_as_prim_step arity =
              let uu____1772 =
                let uu____1773 = FStar_Util.string_of_int arity  in
                Prims.strcat "arrow_as_prim_step_" uu____1773  in
              fstar_syn_emb_prefix uu____1772  in
            let mk_any_embedding s =
              let uu____1780 =
                let uu____1781 =
                  let uu____1788 = fstar_syn_emb_prefix "mk_any_emb"  in
                  let uu____1789 =
                    let uu____1792 = str_to_name s  in [uu____1792]  in
                  (uu____1788, uu____1789)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____1781  in
              FStar_All.pipe_left w uu____1780  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow e1 e2 =
              let uu____1831 =
                let uu____1832 =
                  let uu____1839 = fstar_syn_emb_prefix "e_arrow"  in
                  (uu____1839, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____1832  in
              FStar_All.pipe_left w uu____1831  in
            let known_type_constructors =
              let uu____1853 =
                let uu____1864 =
                  let uu____1875 =
                    let uu____1886 =
                      let uu____1897 =
                        let uu____1906 =
                          FStar_Reflection_Data.fstar_refl_types_lid "term"
                           in
                        (uu____1906, (Prims.parse_int "0"), "term", R)  in
                      let uu____1907 =
                        let uu____1918 =
                          let uu____1927 =
                            FStar_Reflection_Data.fstar_refl_types_lid "fv"
                             in
                          (uu____1927, (Prims.parse_int "0"), "fv", R)  in
                        let uu____1928 =
                          let uu____1939 =
                            let uu____1948 =
                              FStar_Reflection_Data.fstar_refl_types_lid
                                "binder"
                               in
                            (uu____1948, (Prims.parse_int "0"), "binder", R)
                             in
                          let uu____1949 =
                            let uu____1960 =
                              let uu____1969 =
                                FStar_Reflection_Data.fstar_refl_syntax_lid
                                  "binders"
                                 in
                              (uu____1969, (Prims.parse_int "0"), "binders",
                                R)
                               in
                            let uu____1970 =
                              let uu____1981 =
                                let uu____1992 =
                                  let uu____2003 =
                                    let uu____2014 =
                                      let uu____2023 =
                                        FStar_Parser_Const.mk_tuple_lid
                                          (Prims.parse_int "2")
                                          FStar_Range.dummyRange
                                         in
                                      (uu____2023, (Prims.parse_int "2"),
                                        "tuple2", S)
                                       in
                                    let uu____2024 =
                                      let uu____2035 =
                                        let uu____2044 =
                                          FStar_Reflection_Data.fstar_refl_data_lid
                                            "exp"
                                           in
                                        (uu____2044, (Prims.parse_int "0"),
                                          "exp", R)
                                         in
                                      [uu____2035]  in
                                    uu____2014 :: uu____2024  in
                                  (FStar_Parser_Const.option_lid,
                                    (Prims.parse_int "1"), "option", S) ::
                                    uu____2003
                                   in
                                (FStar_Parser_Const.list_lid,
                                  (Prims.parse_int "1"), "list", S) ::
                                  uu____1992
                                 in
                              (FStar_Parser_Const.norm_step_lid,
                                (Prims.parse_int "0"), "norm_step", S) ::
                                uu____1981
                               in
                            uu____1960 :: uu____1970  in
                          uu____1939 :: uu____1949  in
                        uu____1918 :: uu____1928  in
                      uu____1897 :: uu____1907  in
                    (FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                      "string", S) :: uu____1886
                     in
                  (FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                    "unit", S) :: uu____1875
                   in
                (FStar_Parser_Const.bool_lid, (Prims.parse_int "0"), "bool",
                  S) :: uu____1864
                 in
              (FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int", S)
                :: uu____1853
               in
            let is_known_type_constructor fv1 n1 =
              FStar_Util.for_some
                (fun uu____2181  ->
                   match uu____2181 with
                   | (x,args,uu____2192,uu____2193) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                known_type_constructors
               in
            let find_env_entry bv uu____2208 =
              match uu____2208 with
              | (bv',uu____2214) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____2239 =
                let uu____2240 = FStar_Syntax_Subst.compress t3  in
                uu____2240.FStar_Syntax_Syntax.n  in
              match uu____2239 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____2248 =
                    let uu____2249 =
                      let uu____2254 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____2254  in
                    FStar_Pervasives_Native.snd uu____2249  in
                  FStar_All.pipe_left mk_any_embedding uu____2248
              | FStar_Syntax_Syntax.Tm_refine (x,uu____2270) ->
                  mk_embedding env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____2276,uu____2277) ->
                  mk_embedding env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____2350 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____2350 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____2372 =
                           let uu____2373 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____2373  in
                         uu____2372.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____2391 = mk_embedding env t0  in
                       let uu____2392 = mk_embedding env t11  in
                       emb_arrow uu____2391 uu____2392)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____2463 =
                      let uu____2470 =
                        let uu____2471 =
                          let uu____2486 = FStar_Syntax_Syntax.mk_Total tail1
                             in
                          ([b], uu____2486)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____2471  in
                      FStar_Syntax_Syntax.mk uu____2470  in
                    uu____2463 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____2514 ->
                  let uu____2515 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____2515 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____2567 =
                         let uu____2568 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____2568.FStar_Syntax_Syntax.n  in
                       (match uu____2567 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor fv1 n_args ->
                            let arg_embeddings =
                              FStar_List.map
                                (fun uu____2588  ->
                                   match uu____2588 with
                                   | (t4,uu____2596) -> mk_embedding env t4)
                                args
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____2602 =
                              let uu____2611 =
                                FStar_Util.find_opt
                                  (fun uu____2635  ->
                                     match uu____2635 with
                                     | (x,uu____2645,uu____2646,uu____2647)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  known_type_constructors
                                 in
                              FStar_All.pipe_right uu____2611 FStar_Util.must
                               in
                            (match uu____2602 with
                             | (uu____2674,t_arity,_trepr_head,loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _0_20 when _0_20 = (Prims.parse_int "0")
                                      -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____2682 ->
                            let uu____2683 =
                              let uu____2684 =
                                let uu____2685 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.strcat
                                  "Embedding not defined for type "
                                  uu____2685
                                 in
                              NoTacticEmbedding uu____2684  in
                            FStar_Exn.raise uu____2683))
              | FStar_Syntax_Syntax.Tm_uinst uu____2686 ->
                  let uu____2693 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____2693 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____2745 =
                         let uu____2746 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____2746.FStar_Syntax_Syntax.n  in
                       (match uu____2745 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor fv1 n_args ->
                            let arg_embeddings =
                              FStar_List.map
                                (fun uu____2766  ->
                                   match uu____2766 with
                                   | (t4,uu____2774) -> mk_embedding env t4)
                                args
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____2780 =
                              let uu____2789 =
                                FStar_Util.find_opt
                                  (fun uu____2813  ->
                                     match uu____2813 with
                                     | (x,uu____2823,uu____2824,uu____2825)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  known_type_constructors
                                 in
                              FStar_All.pipe_right uu____2789 FStar_Util.must
                               in
                            (match uu____2780 with
                             | (uu____2852,t_arity,_trepr_head,loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _0_21 when _0_21 = (Prims.parse_int "0")
                                      -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____2860 ->
                            let uu____2861 =
                              let uu____2862 =
                                let uu____2863 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.strcat
                                  "Embedding not defined for type "
                                  uu____2863
                                 in
                              NoTacticEmbedding uu____2862  in
                            FStar_Exn.raise uu____2861))
              | FStar_Syntax_Syntax.Tm_app uu____2864 ->
                  let uu____2881 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____2881 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____2933 =
                         let uu____2934 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____2934.FStar_Syntax_Syntax.n  in
                       (match uu____2933 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor fv1 n_args ->
                            let arg_embeddings =
                              FStar_List.map
                                (fun uu____2954  ->
                                   match uu____2954 with
                                   | (t4,uu____2962) -> mk_embedding env t4)
                                args
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____2968 =
                              let uu____2977 =
                                FStar_Util.find_opt
                                  (fun uu____3001  ->
                                     match uu____3001 with
                                     | (x,uu____3011,uu____3012,uu____3013)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  known_type_constructors
                                 in
                              FStar_All.pipe_right uu____2977 FStar_Util.must
                               in
                            (match uu____2968 with
                             | (uu____3040,t_arity,_trepr_head,loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _0_22 when _0_22 = (Prims.parse_int "0")
                                      -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____3048 ->
                            let uu____3049 =
                              let uu____3050 =
                                let uu____3051 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.strcat
                                  "Embedding not defined for type "
                                  uu____3051
                                 in
                              NoTacticEmbedding uu____3050  in
                            FStar_Exn.raise uu____3049))
              | uu____3052 ->
                  let uu____3053 =
                    let uu____3054 =
                      let uu____3055 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.strcat "Embedding not defined for type "
                        uu____3055
                       in
                    NoTacticEmbedding uu____3054  in
                  FStar_Exn.raise uu____3053
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____3072 =
                      let uu____3073 =
                        let uu____3080 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____3081 =
                          let uu____3084 =
                            let uu____3085 =
                              let uu____3086 =
                                let uu____3087 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____3087
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____3086
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____3085
                             in
                          let uu____3088 =
                            let uu____3091 =
                              let uu____3092 =
                                let uu____3093 =
                                  let uu____3094 =
                                    let uu____3101 =
                                      let uu____3104 = str_to_name "args"  in
                                      [uu____3104]  in
                                    (body, uu____3101)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3094
                                   in
                                FStar_All.pipe_left w uu____3093  in
                              mk_lam "_" uu____3092  in
                            [uu____3091]  in
                          uu____3084 :: uu____3088  in
                        (uu____3080, uu____3081)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____3073  in
                    FStar_All.pipe_left w uu____3072  in
                  mk_lam "args" body1
              | uu____3109 ->
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
                    let uu____3146 =
                      let uu____3147 =
                        let uu____3148 =
                          let uu____3155 =
                            let uu____3158 = str_to_name "args"  in
                            [uu____3158]  in
                          (body, uu____3155)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____3148  in
                      FStar_All.pipe_left w uu____3147  in
                    (pattern, FStar_Pervasives_Native.None, uu____3146)  in
                  let default_branch =
                    let uu____3172 =
                      let uu____3173 =
                        let uu____3174 =
                          let uu____3181 = str_to_name "failwith"  in
                          let uu____3182 =
                            let uu____3185 =
                              let uu____3186 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____3186  in
                            [uu____3185]  in
                          (uu____3181, uu____3182)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____3174  in
                      FStar_All.pipe_left w uu____3173  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____3172)
                     in
                  let body1 =
                    let uu____3192 =
                      let uu____3193 =
                        let uu____3208 = str_to_name "args"  in
                        (uu____3208, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____3193  in
                    FStar_All.pipe_left w uu____3192  in
                  let body2 =
                    let uu____3244 =
                      let uu____3245 =
                        let uu____3252 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____3253 =
                          let uu____3256 =
                            let uu____3257 =
                              let uu____3258 =
                                let uu____3259 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____3259
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____3258
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____3257
                             in
                          let uu____3260 =
                            let uu____3263 = mk_lam "_" body1  in
                            [uu____3263]  in
                          uu____3256 :: uu____3260  in
                        (uu____3252, uu____3253)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____3245  in
                    FStar_All.pipe_left w uu____3244  in
                  mk_lam "args" body2
               in
            let uu____3266 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____3266 with
            | (bs,c) ->
                let uu____3305 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____3399 = FStar_Util.first_N n1 bs  in
                           match uu____3399 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____3477 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____3477
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____3492 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____3493 = FStar_Util.string_of_int n1  in
                             let uu____3494 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____3492 uu____3493 uu____3494
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____3305 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____3555 =
                       let uu____3576 =
                         FStar_Util.prefix_until
                           (fun uu____3618  ->
                              match uu____3618 with
                              | (b,uu____3626) ->
                                  let uu____3631 =
                                    let uu____3632 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____3632.FStar_Syntax_Syntax.n  in
                                  (match uu____3631 with
                                   | FStar_Syntax_Syntax.Tm_type uu____3635
                                       -> false
                                   | uu____3636 -> true)) bs1
                          in
                       match uu____3576 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____3555 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____3880 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "tv_" uu____3880) type_vars
                             in
                          let tvar_context =
                            FStar_List.map2
                              (fun b  ->
                                 fun nm  ->
                                   ((FStar_Pervasives_Native.fst b), nm))
                              type_vars tvar_names
                             in
                          let rec aux accum_embeddings bs3 =
                            match bs3 with
                            | [] ->
                                let arg_unembeddings =
                                  FStar_List.rev accum_embeddings  in
                                let res_embedding =
                                  mk_embedding tvar_context result_typ  in
                                let fv_lid2 =
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                let uu____3964 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____3964
                                then
                                  let ncb = str_to_name "ncb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step non_tvar_arity  in
                                  let args =
                                    let uu____3982 =
                                      let uu____3985 =
                                        let uu____3988 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____3989 =
                                          let uu____3992 =
                                            let uu____3993 =
                                              let uu____3994 =
                                                let uu____3995 =
                                                  let uu____4006 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____4006,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____3995
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____3994
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____3993
                                             in
                                          [uu____3992; fv_lid_embedded; ncb]
                                           in
                                        uu____3988 :: uu____3989  in
                                      res_embedding :: uu____3985  in
                                    FStar_List.append arg_unembeddings
                                      uu____3982
                                     in
                                  let fun_embedding =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (embed_fun_N, args))
                                     in
                                  let tabs =
                                    abstract_tvars tvar_names fun_embedding
                                     in
                                  let uu____4027 =
                                    let uu____4028 = mk_lam "ncb" tabs  in
                                    mk_lam "_psc" uu____4028  in
                                  (uu____4027, arity, true)
                                else
                                  (let uu____4034 =
                                     let uu____4035 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____4035
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____4034
                                   then
                                     let h =
                                       let uu____4043 =
                                         let uu____4044 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.strcat
                                           "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
                                           uu____4044
                                          in
                                       str_to_top_name uu____4043  in
                                     let tac_fun =
                                       let uu____4052 =
                                         let uu____4053 =
                                           let uu____4060 =
                                             let uu____4061 =
                                               let uu____4062 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.strcat
                                                 "FStar_Tactics_Native.from_tactic_"
                                                 uu____4062
                                                in
                                             str_to_top_name uu____4061  in
                                           let uu____4069 =
                                             let uu____4072 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____4072]  in
                                           (uu____4060, uu____4069)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____4053
                                          in
                                       FStar_All.pipe_left w uu____4052  in
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
                                           let uu____4082 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____4082
                                       | uu____4085 ->
                                           let uu____4088 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____4088
                                        in
                                     let uu____4091 =
                                       let uu____4092 = mk_lam "ncb" tabs  in
                                       mk_lam "psc" uu____4092  in
                                     (uu____4091,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____4100 =
                                        let uu____4101 =
                                          let uu____4102 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.strcat
                                            "Plugins not defined for type "
                                            uu____4102
                                           in
                                        NoTacticEmbedding uu____4101  in
                                      FStar_Exn.raise uu____4100))
                            | (b,uu____4110)::bs4 ->
                                let uu____4130 =
                                  let uu____4133 =
                                    mk_embedding tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____4133 :: accum_embeddings  in
                                aux uu____4130 bs4
                             in
                          (try
                             (fun uu___267_4144  ->
                                match () with
                                | () ->
                                    let uu____4153 = aux [] bs2  in
                                    FStar_Pervasives_Native.Some uu____4153)
                               ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____4180 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____4180 msg);
                                FStar_Pervasives_Native.None))))
  