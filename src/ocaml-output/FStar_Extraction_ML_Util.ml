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
      try (fun uu___274_103  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___273_106 ->
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
          (fun _0_1  -> FStar_Extraction_ML_Syntax.MLE_Const _0_1)
         in
      FStar_All.pipe_right uu____121
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____151 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_2  -> FStar_Extraction_ML_Syntax.MLE_Const _0_2)
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
    fun uu___266_364  ->
      match uu___266_364 with
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
  fun uu___267_415  ->
    match uu___267_415 with
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
                               (fun _0_3  ->
                                  FStar_Pervasives_Native.Some _0_3)
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
  fun uu___268_1002  ->
    match uu___268_1002 with
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
  fun uu___269_1111  ->
    match uu___269_1111 with
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
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____1635 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____1641 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____1647 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____1653 -> false
  
type wrapped_term =
  (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlexpr,
    Prims.int,Prims.bool) FStar_Pervasives_Native.tuple4
let (interpret_plugin_as_term_fun :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ ->
        Prims.int FStar_Pervasives_Native.option ->
          FStar_Extraction_ML_Syntax.mlexpr' ->
            (FStar_Extraction_ML_Syntax.mlexpr,FStar_Extraction_ML_Syntax.mlexpr,
              Prims.int,Prims.bool) FStar_Pervasives_Native.tuple4
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
              let uu____1716 =
                let uu____1717 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____1717  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1716
               in
            let lid_to_top_name l =
              let uu____1724 =
                let uu____1725 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____1725  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1724
               in
            let str_to_name s =
              let uu____1732 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____1732  in
            let str_to_top_name s =
              let uu____1739 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____1739  in
            let fstar_tc_nbe_prefix s =
              str_to_name (Prims.strcat "FStar_TypeChecker_NBETerm." s)  in
            let fstar_syn_emb_prefix s =
              str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)  in
            let fstar_refl_emb_prefix s =
              str_to_name (Prims.strcat "FStar_Reflection_Embeddings." s)  in
            let fstar_refl_nbeemb_prefix s =
              str_to_name (Prims.strcat "FStar_Reflection_NBEEmbeddings." s)
               in
            let fv_lid_embedded =
              let uu____1765 =
                let uu____1766 =
                  let uu____1773 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____1774 =
                    let uu____1777 =
                      let uu____1778 =
                        let uu____1779 =
                          let uu____1780 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____1780
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____1779  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1778
                       in
                    [uu____1777]  in
                  (uu____1773, uu____1774)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____1766  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____1765
               in
            let emb_prefix uu___270_1793 =
              match uu___270_1793 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____1803 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____1810 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.strcat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____1833 =
                let uu____1834 = FStar_Util.string_of_int arity  in
                Prims.strcat "arrow_as_prim_step_" uu____1834  in
              emb_prefix l uu____1833  in
            let mk_any_embedding l s =
              let uu____1846 =
                let uu____1847 =
                  let uu____1854 = emb_prefix l "mk_any_emb"  in
                  let uu____1855 =
                    let uu____1858 = str_to_name s  in [uu____1858]  in
                  (uu____1854, uu____1855)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____1847  in
              FStar_All.pipe_left w uu____1846  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____1902 =
                let uu____1903 =
                  let uu____1910 = emb_prefix l "e_arrow"  in
                  (uu____1910, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____1903  in
              FStar_All.pipe_left w uu____1902  in
            let known_type_constructors =
              let term_cs =
                let uu____1943 =
                  let uu____1956 =
                    let uu____1969 =
                      let uu____1982 =
                        let uu____1995 =
                          let uu____2008 =
                            let uu____2021 =
                              let uu____2034 =
                                let uu____2045 =
                                  let uu____2052 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____2052, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____2045, Syntax_term)  in
                              let uu____2059 =
                                let uu____2072 =
                                  let uu____2083 =
                                    let uu____2090 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____2090, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____2083, Refl_emb)  in
                                let uu____2097 =
                                  let uu____2110 =
                                    let uu____2121 =
                                      let uu____2128 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____2128, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____2121, Refl_emb)  in
                                  let uu____2135 =
                                    let uu____2148 =
                                      let uu____2159 =
                                        let uu____2166 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____2166, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____2159, Refl_emb)  in
                                    let uu____2173 =
                                      let uu____2186 =
                                        let uu____2197 =
                                          let uu____2204 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____2204, (Prims.parse_int "0"),
                                            "binders")
                                           in
                                        (uu____2197, Refl_emb)  in
                                      let uu____2211 =
                                        let uu____2224 =
                                          let uu____2235 =
                                            let uu____2242 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____2242,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____2235, Refl_emb)  in
                                        [uu____2224]  in
                                      uu____2186 :: uu____2211  in
                                    uu____2148 :: uu____2173  in
                                  uu____2110 :: uu____2135  in
                                uu____2072 :: uu____2097  in
                              uu____2034 :: uu____2059  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____2021
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____2008
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____1995
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____1982
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____1969
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____1956
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____1943
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___271_2466  ->
                     match uu___271_2466 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____2525 -> failwith "Impossible") term_cs
                 in
              fun uu___272_2546  ->
                match uu___272_2546 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____2559 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____2591  ->
                   match uu____2591 with
                   | ((x,args,uu____2604),uu____2605) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____2626 =
              match uu____2626 with
              | (bv',uu____2632) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____2662 =
                let uu____2663 = FStar_Syntax_Subst.compress t3  in
                uu____2663.FStar_Syntax_Syntax.n  in
              match uu____2662 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____2671 =
                    let uu____2672 =
                      let uu____2677 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____2677  in
                    FStar_Pervasives_Native.snd uu____2672  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____2671
              | FStar_Syntax_Syntax.Tm_refine (x,uu____2693) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____2699,uu____2700) ->
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____2773 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____2773 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____2795 =
                           let uu____2796 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____2796  in
                         uu____2795.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____2814 = mk_embedding l env t0  in
                       let uu____2815 = mk_embedding l env t11  in
                       emb_arrow l uu____2814 uu____2815)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____2886 =
                      let uu____2893 =
                        let uu____2894 =
                          let uu____2909 = FStar_Syntax_Syntax.mk_Total tail1
                             in
                          ([b], uu____2909)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____2894  in
                      FStar_Syntax_Syntax.mk uu____2893  in
                    uu____2886 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____2937 ->
                  let uu____2938 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____2938 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____2990 =
                         let uu____2991 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____2991.FStar_Syntax_Syntax.n  in
                       (match uu____2990 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3021  ->
                                      match uu____3021 with
                                      | (t4,uu____3029) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3035 =
                              let uu____3046 =
                                FStar_Util.find_opt
                                  (fun uu____3074  ->
                                     match uu____3074 with
                                     | ((x,uu____3086,uu____3087),uu____3088)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3046 FStar_Util.must
                               in
                            (match uu____3035 with
                             | ((uu____3127,t_arity,_trepr_head),loc_embedding)
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
                        | uu____3141 ->
                            let uu____3142 =
                              let uu____3143 =
                                let uu____3144 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.strcat
                                  "Embedding not defined for type "
                                  uu____3144
                                 in
                              NoTacticEmbedding uu____3143  in
                            FStar_Exn.raise uu____3142))
              | FStar_Syntax_Syntax.Tm_uinst uu____3145 ->
                  let uu____3152 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3152 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3204 =
                         let uu____3205 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____3205.FStar_Syntax_Syntax.n  in
                       (match uu____3204 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3235  ->
                                      match uu____3235 with
                                      | (t4,uu____3243) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3249 =
                              let uu____3260 =
                                FStar_Util.find_opt
                                  (fun uu____3288  ->
                                     match uu____3288 with
                                     | ((x,uu____3300,uu____3301),uu____3302)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3260 FStar_Util.must
                               in
                            (match uu____3249 with
                             | ((uu____3341,t_arity,_trepr_head),loc_embedding)
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
                        | uu____3355 ->
                            let uu____3356 =
                              let uu____3357 =
                                let uu____3358 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.strcat
                                  "Embedding not defined for type "
                                  uu____3358
                                 in
                              NoTacticEmbedding uu____3357  in
                            FStar_Exn.raise uu____3356))
              | FStar_Syntax_Syntax.Tm_app uu____3359 ->
                  let uu____3376 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____3376 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____3428 =
                         let uu____3429 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____3429.FStar_Syntax_Syntax.n  in
                       (match uu____3428 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____3459  ->
                                      match uu____3459 with
                                      | (t4,uu____3467) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____3473 =
                              let uu____3484 =
                                FStar_Util.find_opt
                                  (fun uu____3512  ->
                                     match uu____3512 with
                                     | ((x,uu____3524,uu____3525),uu____3526)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____3484 FStar_Util.must
                               in
                            (match uu____3473 with
                             | ((uu____3565,t_arity,_trepr_head),loc_embedding)
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
                        | uu____3579 ->
                            let uu____3580 =
                              let uu____3581 =
                                let uu____3582 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.strcat
                                  "Embedding not defined for type "
                                  uu____3582
                                 in
                              NoTacticEmbedding uu____3581  in
                            FStar_Exn.raise uu____3580))
              | uu____3583 ->
                  let uu____3584 =
                    let uu____3585 =
                      let uu____3586 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.strcat "Embedding not defined for type "
                        uu____3586
                       in
                    NoTacticEmbedding uu____3585  in
                  FStar_Exn.raise uu____3584
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____3603 =
                      let uu____3604 =
                        let uu____3611 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____3612 =
                          let uu____3615 =
                            let uu____3616 =
                              let uu____3617 =
                                let uu____3618 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____3618
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____3617
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____3616
                             in
                          let uu____3619 =
                            let uu____3622 =
                              let uu____3623 =
                                let uu____3624 =
                                  let uu____3625 =
                                    let uu____3632 =
                                      let uu____3635 = str_to_name "args"  in
                                      [uu____3635]  in
                                    (body, uu____3632)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____3625
                                   in
                                FStar_All.pipe_left w uu____3624  in
                              mk_lam "_" uu____3623  in
                            [uu____3622]  in
                          uu____3615 :: uu____3619  in
                        (uu____3611, uu____3612)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____3604  in
                    FStar_All.pipe_left w uu____3603  in
                  mk_lam "args" body1
              | uu____3640 ->
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
                    let uu____3677 =
                      let uu____3678 =
                        let uu____3679 =
                          let uu____3686 =
                            let uu____3689 = str_to_name "args"  in
                            [uu____3689]  in
                          (body, uu____3686)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____3679  in
                      FStar_All.pipe_left w uu____3678  in
                    (pattern, FStar_Pervasives_Native.None, uu____3677)  in
                  let default_branch =
                    let uu____3703 =
                      let uu____3704 =
                        let uu____3705 =
                          let uu____3712 = str_to_name "failwith"  in
                          let uu____3713 =
                            let uu____3716 =
                              let uu____3717 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____3717  in
                            [uu____3716]  in
                          (uu____3712, uu____3713)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____3705  in
                      FStar_All.pipe_left w uu____3704  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____3703)
                     in
                  let body1 =
                    let uu____3723 =
                      let uu____3724 =
                        let uu____3739 = str_to_name "args"  in
                        (uu____3739, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____3724  in
                    FStar_All.pipe_left w uu____3723  in
                  let body2 =
                    let uu____3775 =
                      let uu____3776 =
                        let uu____3783 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____3784 =
                          let uu____3787 =
                            let uu____3788 =
                              let uu____3789 =
                                let uu____3790 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____3790
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____3789
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____3788
                             in
                          let uu____3791 =
                            let uu____3794 = mk_lam "_" body1  in
                            [uu____3794]  in
                          uu____3787 :: uu____3791  in
                        (uu____3783, uu____3784)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____3776  in
                    FStar_All.pipe_left w uu____3775  in
                  mk_lam "args" body2
               in
            let uu____3797 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____3797 with
            | (bs,c) ->
                let uu____3830 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____3924 = FStar_Util.first_N n1 bs  in
                           match uu____3924 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____4002 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____4002
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____4017 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____4018 = FStar_Util.string_of_int n1  in
                             let uu____4019 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____4017 uu____4018 uu____4019
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____3830 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____4074 =
                       let uu____4095 =
                         FStar_Util.prefix_until
                           (fun uu____4137  ->
                              match uu____4137 with
                              | (b,uu____4145) ->
                                  let uu____4150 =
                                    let uu____4151 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____4151.FStar_Syntax_Syntax.n  in
                                  (match uu____4150 with
                                   | FStar_Syntax_Syntax.Tm_type uu____4154
                                       -> false
                                   | uu____4155 -> true)) bs1
                          in
                       match uu____4095 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____4074 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____4393 =
                                     FStar_Util.string_of_int i  in
                                   Prims.strcat "tv_" uu____4393) type_vars
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
                                let uu____4482 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____4482
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____4498 =
                                      let uu____4501 =
                                        let uu____4504 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____4505 =
                                          let uu____4508 =
                                            let uu____4509 =
                                              let uu____4510 =
                                                let uu____4511 =
                                                  let uu____4522 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____4522,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____4511
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____4510
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____4509
                                             in
                                          [uu____4508; fv_lid_embedded; cb]
                                           in
                                        uu____4504 :: uu____4505  in
                                      res_embedding :: uu____4501  in
                                    FStar_List.append arg_unembeddings
                                      uu____4498
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
                                  let uu____4544 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____4544, arity, true)
                                else
                                  (let uu____4551 =
                                     let uu____4552 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____4552
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____4551
                                   then
                                     let h =
                                       let uu____4560 =
                                         let uu____4561 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.strcat
                                           (mk_tactic_interpretation loc)
                                           uu____4561
                                          in
                                       str_to_top_name uu____4560  in
                                     let tac_fun =
                                       let uu____4569 =
                                         let uu____4570 =
                                           let uu____4577 =
                                             let uu____4578 =
                                               let uu____4579 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.strcat
                                                 (mk_from_tactic loc)
                                                 uu____4579
                                                in
                                             str_to_top_name uu____4578  in
                                           let uu____4586 =
                                             let uu____4589 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____4589]  in
                                           (uu____4577, uu____4586)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____4570
                                          in
                                       FStar_All.pipe_left w uu____4569  in
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
                                           let uu____4599 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____4599
                                       | uu____4602 ->
                                           let uu____4605 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____4605
                                        in
                                     let uu____4608 =
                                       let uu____4609 = mk_lam "ncb" tabs  in
                                       mk_lam "psc" uu____4609  in
                                     (uu____4608,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____4617 =
                                        let uu____4618 =
                                          let uu____4619 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.strcat
                                            "Plugins not defined for type "
                                            uu____4619
                                           in
                                        NoTacticEmbedding uu____4618  in
                                      FStar_Exn.raise uu____4617))
                            | (b,uu____4627)::bs4 ->
                                let uu____4647 =
                                  let uu____4650 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____4650 :: accum_embeddings  in
                                aux loc uu____4647 bs4
                             in
                          (try
                             (fun uu___276_4670  ->
                                match () with
                                | () ->
                                    let uu____4681 = aux Syntax_term [] bs2
                                       in
                                    (match uu____4681 with
                                     | (w1,a,b) ->
                                         let uu____4701 = aux NBE_t [] bs2
                                            in
                                         (match uu____4701 with
                                          | (w',uu____4719,uu____4720) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____4745 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____4745 msg);
                                FStar_Pervasives_Native.None))))
  