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
    | FStar_Const.Const_range uu____93 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____123) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____129) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____134 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____138 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try (fun uu___51_156  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___50_159 ->
          let uu____160 =
            let uu____162 = FStar_Range.string_of_range p  in
            let uu____164 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____162 uu____164
             in
          failwith uu____160
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____187 =
        let uu____188 =
          let uu____189 =
            let uu____201 = FStar_Util.string_of_int i  in
            (uu____201, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____189  in
        FStar_All.pipe_right uu____188
          (fun _214  -> FStar_Extraction_ML_Syntax.MLE_Const _214)
         in
      FStar_All.pipe_right uu____187
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____232 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _233  -> FStar_Extraction_ML_Syntax.MLE_Const _233)
         in
      FStar_All.pipe_right uu____232
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____237 =
      let uu____250 =
        let uu____256 =
          let uu____263 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____263 cstr  in
        let uu____269 =
          let uu____275 =
            let uu____282 =
              let uu____284 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____284 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____282 cint  in
          let uu____290 =
            let uu____296 =
              let uu____303 =
                let uu____305 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____305 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____303 cint  in
            let uu____311 =
              let uu____317 =
                let uu____324 =
                  let uu____326 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____326 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____324 cint  in
              let uu____332 =
                let uu____338 =
                  let uu____345 =
                    let uu____347 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____347 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____345 cint  in
                [uu____338]  in
              uu____317 :: uu____332  in
            uu____296 :: uu____311  in
          uu____275 :: uu____290  in
        uu____256 :: uu____269  in
      (mk_range_mle, uu____250)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____237
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____391 ->
          let uu____392 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____392
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____420 =
            FStar_Util.find_opt
              (fun uu____436  ->
                 match uu____436 with | (y,uu____444) -> y = x) subst1
             in
          (match uu____420 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____468 =
            let uu____475 = subst_aux subst1 t1  in
            let uu____476 = subst_aux subst1 t2  in (uu____475, f, uu____476)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____468
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____483 =
            let uu____490 = FStar_List.map (subst_aux subst1) args  in
            (uu____490, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____483
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____498 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____498
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____514  ->
    fun args  ->
      match uu____514 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____528 =
               let uu____529 = FStar_List.zip formals args  in
               subst_aux uu____529 t  in
             FStar_Pervasives_Native.Some uu____528)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____561 = try_subst ts args  in
      match uu____561 with
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
    fun uu___0_637  ->
      match uu___0_637 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____705 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____705 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____711 = try_subst ts args  in
               (match uu____711 with
                | FStar_Pervasives_Native.None  ->
                    let uu____716 =
                      let uu____718 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____720 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____722 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____718 uu____720 uu____722
                       in
                    failwith uu____716
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____729 -> FStar_Pervasives_Native.None)
      | uu____732 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____746) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____750 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___1_762  ->
    match uu___1_762 with
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
        | uu____783 ->
            let uu____788 =
              let uu____790 = FStar_Range.string_of_range r  in
              let uu____792 = eff_to_string f  in
              let uu____794 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____790
                uu____792 uu____794
               in
            failwith uu____788
  
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
    (fun uu____837  ->
       fun t  ->
         match uu____837 with
         | (uu____844,t0) ->
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
                | uu____1003 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____1049 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____1060 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____1060 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____1074;
                     FStar_Extraction_ML_Syntax.loc = uu____1075;_}
                   ->
                   let uu____1109 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____1109
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____1133 = type_leq unfold_ty t2 t2'  in
                        (if uu____1133
                         then
                           let body1 =
                             let uu____1153 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____1153
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____1167 =
                             let uu____1173 =
                               let uu____1180 =
                                 let uu____1188 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____1188
                                  in
                               FStar_All.pipe_left uu____1180
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____1173  in
                           (true, uu____1167)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____1246 =
                           let uu____1257 =
                             let uu____1263 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _1281  ->
                                  FStar_Pervasives_Native.Some _1281)
                               uu____1263
                              in
                           type_leq_c unfold_ty uu____1257 t2 t2'  in
                         match uu____1246 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____1324 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____1324
                               | uu____1344 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____1371 ->
                   let uu____1377 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____1377
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____1432 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____1432
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____1466 = unfold_ty t  in
                 match uu____1466 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____1480 = unfold_ty t'  in
                     (match uu____1480 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____1510 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____1510
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____1549,uu____1550) ->
              let uu____1557 = unfold_ty t  in
              (match uu____1557 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____1571 -> (false, FStar_Pervasives_Native.None))
          | (uu____1584,FStar_Extraction_ML_Syntax.MLTY_Named uu____1585) ->
              let uu____1592 = unfold_ty t'  in
              (match uu____1592 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____1606 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____1626 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____1646 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____1646 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1686 =
          let uu____1693 = erase_effect_annotations t1  in
          let uu____1694 = erase_effect_annotations t2  in
          (uu____1693, FStar_Extraction_ML_Syntax.E_PURE, uu____1694)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____1686
    | uu____1695 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___2_1723  ->
    match uu___2_1723 with
    | (FStar_Util.Inl uu____1735,uu____1736)::uu____1737 -> true
    | uu____1761 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1789  ->
    match uu____1789 with
    | (ns,n1) ->
        let uu____1811 =
          let uu____1813 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____1813  in
        if uu____1811
        then
          let uu____1823 =
            let uu____1825 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____1825  in
          FStar_Pervasives_Native.Some uu____1823
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1862 = is_xtuple mlp  in
        (match uu____1862 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1875 -> e)
    | uu____1879 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___3_1894  ->
    match uu___3_1894 with
    | f::uu____1905 ->
        let uu____1920 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1920 with
         | (ns,uu____1937) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1964 -> failwith "impos"
  
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
  fun uu____2050  ->
    match uu____2050 with
    | (ns,n1) ->
        let uu____2072 =
          let uu____2074 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____2074  in
        if uu____2072
        then
          let uu____2084 =
            let uu____2086 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____2086  in
          FStar_Pervasives_Native.Some uu____2084
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____2105 = is_xtuple_ty mlp  in
        (match uu____2105 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____2112 -> t)
    | uu____2116 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____2130 = codegen_fsharp ()  in
    if uu____2130
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____2152  ->
    match uu____2152 with
    | (ns,n1) ->
        let uu____2172 = codegen_fsharp ()  in
        if uu____2172
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____2208 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____2208, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____2245 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____2245
      then true
      else
        (let uu____2252 = unfold_ty t  in
         match uu____2252 with
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
            let uu____2275 =
              let uu____2282 = eraseTypeDeep unfold_ty tyd  in
              let uu____2283 = eraseTypeDeep unfold_ty tycd  in
              (uu____2282, etag, uu____2283)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____2275
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____2292 = erasableType unfold_ty t  in
          if uu____2292
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____2297 =
               let uu____2304 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____2304, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____2297)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____2312 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____2312
      | uu____2315 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____2341 =
    let uu____2349 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____2349  in
  FStar_All.pipe_left uu____2341
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
          let uu____2566 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____2566
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____2591 = FStar_Range.file_of_range r  in (line, uu____2591)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____2614,b) ->
        let uu____2616 = doms_and_cod b  in
        (match uu____2616 with | (ds,c) -> ((a :: ds), c))
    | uu____2637 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____2650 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____2650
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____2678,b) ->
        let uu____2680 = uncurry_mlty_fun b  in
        (match uu____2680 with | (args,res) -> ((a :: args), res))
    | uu____2701 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____2717 -> true
    | uu____2720 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____2730 -> uu____2730
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____2752 =
          let uu____2758 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____2758)  in
        FStar_Errors.log_issue r uu____2752
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____2771 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____2782 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____2793 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____2804 -> false
  
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
              let uu____3049 =
                let uu____3050 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____3050  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____3049
               in
            let lid_to_top_name l =
              let uu____3071 =
                let uu____3072 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____3072  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____3071
               in
            let str_to_name s =
              let uu____3087 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____3087  in
            let str_to_top_name s =
              let uu____3107 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____3107  in
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
              let uu____3171 =
                let uu____3172 =
                  let uu____3185 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____3193 =
                    let uu____3199 =
                      let uu____3206 =
                        let uu____3207 =
                          let uu____3208 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____3208
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____3207  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____3206
                       in
                    [uu____3199]  in
                  (uu____3185, uu____3193)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____3172  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____3171
               in
            let emb_prefix uu___4_3244 =
              match uu___4_3244 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____3261 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____3272 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____3313 =
                let uu____3315 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____3315  in
              emb_prefix l uu____3313  in
            let mk_any_embedding l s =
              let uu____3337 =
                let uu____3338 =
                  let uu____3351 = emb_prefix l "mk_any_emb"  in
                  let uu____3359 =
                    let uu____3365 = str_to_name s  in [uu____3365]  in
                  (uu____3351, uu____3359)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____3338  in
              FStar_All.pipe_left w uu____3337  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____3466 =
                let uu____3467 =
                  let uu____3480 = emb_prefix l "e_arrow"  in
                  (uu____3480, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____3467  in
              FStar_All.pipe_left w uu____3466  in
            let known_type_constructors =
              let term_cs =
                let uu____3550 =
                  let uu____3569 =
                    let uu____3588 =
                      let uu____3607 =
                        let uu____3626 =
                          let uu____3645 =
                            let uu____3664 =
                              let uu____3683 =
                                let uu____3700 =
                                  let uu____3713 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____3713, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____3700, Syntax_term)  in
                              let uu____3743 =
                                let uu____3762 =
                                  let uu____3779 =
                                    let uu____3792 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____3792, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____3779, Refl_emb)  in
                                let uu____3822 =
                                  let uu____3841 =
                                    let uu____3858 =
                                      let uu____3871 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____3871, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____3858, Refl_emb)  in
                                  let uu____3901 =
                                    let uu____3920 =
                                      let uu____3937 =
                                        let uu____3950 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____3950, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____3937, Refl_emb)  in
                                    let uu____3980 =
                                      let uu____3999 =
                                        let uu____4016 =
                                          let uu____4029 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____4029, (Prims.parse_int "0"),
                                            "binders")
                                           in
                                        (uu____4016, Refl_emb)  in
                                      let uu____4059 =
                                        let uu____4078 =
                                          let uu____4095 =
                                            let uu____4108 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____4108,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____4095, Refl_emb)  in
                                        [uu____4078]  in
                                      uu____3999 :: uu____4059  in
                                    uu____3920 :: uu____3980  in
                                  uu____3841 :: uu____3901  in
                                uu____3762 :: uu____3822  in
                              uu____3683 :: uu____3743  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____3664
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____3645
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____3626
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____3607
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____3588
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____3569
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____3550
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___5_4555  ->
                     match uu___5_4555 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____4662 -> failwith "Impossible") term_cs
                 in
              fun uu___6_4696  ->
                match uu___6_4696 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____4715 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____4762  ->
                   match uu____4762 with
                   | ((x,args,uu____4782),uu____4783) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____4835 =
              match uu____4835 with
              | (bv',uu____4853) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____4929 =
                let uu____4930 = FStar_Syntax_Subst.compress t3  in
                uu____4930.FStar_Syntax_Syntax.n  in
              match uu____4929 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____4960 =
                    let uu____4962 =
                      let uu____4973 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____4973  in
                    FStar_Pervasives_Native.snd uu____4962  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____4960
              | FStar_Syntax_Syntax.Tm_refine (x,uu____5017) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____5041,uu____5042) ->
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____5183 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____5183 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____5238 =
                           let uu____5249 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____5249  in
                         uu____5238.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____5290 = mk_embedding l env t0  in
                       let uu____5297 = mk_embedding l env t11  in
                       emb_arrow l uu____5290 uu____5297)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____5442 =
                      let uu____5449 =
                        let uu____5450 =
                          let uu____5474 = FStar_Syntax_Syntax.mk_Total tail1
                             in
                          ([b], uu____5474)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____5450  in
                      FStar_Syntax_Syntax.mk uu____5449  in
                    uu____5442 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____5526 ->
                  let uu____5530 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____5530 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____5613 =
                         let uu____5614 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____5614.FStar_Syntax_Syntax.n  in
                       (match uu____5613 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____5671  ->
                                      match uu____5671 with
                                      | (t4,uu____5686) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____5705 =
                              let uu____5722 =
                                FStar_Util.find_opt
                                  (fun uu____5762  ->
                                     match uu____5762 with
                                     | ((x,uu____5781,uu____5782),uu____5783)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____5722 FStar_Util.must
                               in
                            (match uu____5705 with
                             | ((uu____5861,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _5899 when _5899 = (Prims.parse_int "0")
                                      -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____5913 ->
                            let uu____5914 =
                              let uu____5915 =
                                let uu____5917 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____5917
                                 in
                              NoTacticEmbedding uu____5915  in
                            FStar_Exn.raise uu____5914))
              | FStar_Syntax_Syntax.Tm_uinst uu____5923 ->
                  let uu____5934 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____5934 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____6017 =
                         let uu____6018 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____6018.FStar_Syntax_Syntax.n  in
                       (match uu____6017 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____6075  ->
                                      match uu____6075 with
                                      | (t4,uu____6090) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____6109 =
                              let uu____6126 =
                                FStar_Util.find_opt
                                  (fun uu____6166  ->
                                     match uu____6166 with
                                     | ((x,uu____6185,uu____6186),uu____6187)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____6126 FStar_Util.must
                               in
                            (match uu____6109 with
                             | ((uu____6265,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _6303 when _6303 = (Prims.parse_int "0")
                                      -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____6317 ->
                            let uu____6318 =
                              let uu____6319 =
                                let uu____6321 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____6321
                                 in
                              NoTacticEmbedding uu____6319  in
                            FStar_Exn.raise uu____6318))
              | FStar_Syntax_Syntax.Tm_app uu____6327 ->
                  let uu____6352 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____6352 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____6435 =
                         let uu____6436 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____6436.FStar_Syntax_Syntax.n  in
                       (match uu____6435 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____6493  ->
                                      match uu____6493 with
                                      | (t4,uu____6508) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____6527 =
                              let uu____6544 =
                                FStar_Util.find_opt
                                  (fun uu____6584  ->
                                     match uu____6584 with
                                     | ((x,uu____6603,uu____6604),uu____6605)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____6544 FStar_Util.must
                               in
                            (match uu____6527 with
                             | ((uu____6683,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _6721 when _6721 = (Prims.parse_int "0")
                                      -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____6735 ->
                            let uu____6736 =
                              let uu____6737 =
                                let uu____6739 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____6739
                                 in
                              NoTacticEmbedding uu____6737  in
                            FStar_Exn.raise uu____6736))
              | uu____6745 ->
                  let uu____6746 =
                    let uu____6747 =
                      let uu____6749 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____6749
                       in
                    NoTacticEmbedding uu____6747  in
                  FStar_Exn.raise uu____6746
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____6792 =
                      let uu____6793 =
                        let uu____6806 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____6814 =
                          let uu____6820 =
                            let uu____6827 =
                              let uu____6828 =
                                let uu____6829 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____6829
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____6828
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____6827
                             in
                          let uu____6834 =
                            let uu____6840 =
                              let uu____6847 =
                                let uu____6854 =
                                  let uu____6855 =
                                    let uu____6868 =
                                      let uu____6874 = str_to_name "args"  in
                                      [uu____6874]  in
                                    (body, uu____6868)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____6855
                                   in
                                FStar_All.pipe_left w uu____6854  in
                              mk_lam "_" uu____6847  in
                            [uu____6840]  in
                          uu____6820 :: uu____6834  in
                        (uu____6806, uu____6814)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____6793  in
                    FStar_All.pipe_left w uu____6792  in
                  mk_lam "args" body1
              | uu____6921 ->
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
                    let uu____6976 =
                      let uu____6983 =
                        let uu____6984 =
                          let uu____6997 =
                            let uu____7003 = str_to_name "args"  in
                            [uu____7003]  in
                          (body, uu____6997)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____6984  in
                      FStar_All.pipe_left w uu____6983  in
                    (pattern, FStar_Pervasives_Native.None, uu____6976)  in
                  let default_branch =
                    let uu____7054 =
                      let uu____7061 =
                        let uu____7062 =
                          let uu____7075 = str_to_name "failwith"  in
                          let uu____7083 =
                            let uu____7089 =
                              let uu____7096 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____7096  in
                            [uu____7089]  in
                          (uu____7075, uu____7083)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____7062  in
                      FStar_All.pipe_left w uu____7061  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____7054)
                     in
                  let body1 =
                    let uu____7137 =
                      let uu____7138 =
                        let uu____7162 = str_to_name "args"  in
                        (uu____7162, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____7138  in
                    FStar_All.pipe_left w uu____7137  in
                  let body2 =
                    let uu____7241 =
                      let uu____7242 =
                        let uu____7255 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____7263 =
                          let uu____7269 =
                            let uu____7276 =
                              let uu____7277 =
                                let uu____7278 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____7278
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const uu____7277
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____7276
                             in
                          let uu____7283 =
                            let uu____7289 = mk_lam "_" body1  in
                            [uu____7289]  in
                          uu____7269 :: uu____7283  in
                        (uu____7255, uu____7263)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____7242  in
                    FStar_All.pipe_left w uu____7241  in
                  mk_lam "args" body2
               in
            let uu____7318 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____7318 with
            | (bs,c) ->
                let uu____7378 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____7530 = FStar_Util.first_N n1 bs  in
                           match uu____7530 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____7660 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____7660
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____7702 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____7704 = FStar_Util.string_of_int n1  in
                             let uu____7706 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____7702 uu____7704 uu____7706
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____7378 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____7797 =
                       let uu____7828 =
                         FStar_Util.prefix_until
                           (fun uu____7890  ->
                              match uu____7890 with
                              | (b,uu____7904) ->
                                  let uu____7919 =
                                    let uu____7920 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____7920.FStar_Syntax_Syntax.n  in
                                  (match uu____7919 with
                                   | FStar_Syntax_Syntax.Tm_type uu____7932
                                       -> false
                                   | uu____7934 -> true)) bs1
                          in
                       match uu____7828 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____7797 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____8316 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____8316) type_vars
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
                                let uu____8497 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____8497
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____8532 =
                                      let uu____8538 =
                                        let uu____8544 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____8551 =
                                          let uu____8557 =
                                            let uu____8564 =
                                              let uu____8565 =
                                                let uu____8566 =
                                                  let uu____8578 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____8578,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____8566
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____8565
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____8564
                                             in
                                          [uu____8557; fv_lid_embedded; cb]
                                           in
                                        uu____8544 :: uu____8551  in
                                      res_embedding :: uu____8538  in
                                    FStar_List.append arg_unembeddings
                                      uu____8532
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
                                  let uu____8648 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____8648, arity, true)
                                else
                                  (let uu____8670 =
                                     let uu____8672 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____8672
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____8670
                                   then
                                     let h =
                                       let uu____8700 =
                                         let uu____8702 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____8702
                                          in
                                       str_to_top_name uu____8700  in
                                     let tac_fun =
                                       let uu____8711 =
                                         let uu____8712 =
                                           let uu____8725 =
                                             let uu____8732 =
                                               let uu____8734 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____8734
                                                in
                                             str_to_top_name uu____8732  in
                                           let uu____8736 =
                                             let uu____8742 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____8742]  in
                                           (uu____8725, uu____8736)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____8712
                                          in
                                       FStar_All.pipe_left w uu____8711  in
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
                                           let uu____8831 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____8831
                                       | uu____8859 ->
                                           let uu____8863 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____8863
                                        in
                                     let uu____8881 =
                                       let uu____8888 = mk_lam "ncb" tabs  in
                                       mk_lam "psc" uu____8888  in
                                     (uu____8881,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____8906 =
                                        let uu____8907 =
                                          let uu____8909 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____8909
                                           in
                                        NoTacticEmbedding uu____8907  in
                                      FStar_Exn.raise uu____8906))
                            | (b,uu____8924)::bs4 ->
                                let uu____8964 =
                                  let uu____8970 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____8970 :: accum_embeddings  in
                                aux loc uu____8964 bs4
                             in
                          (try
                             (fun uu___687_9007  ->
                                match () with
                                | () ->
                                    let uu____9026 = aux Syntax_term [] bs2
                                       in
                                    (match uu____9026 with
                                     | (w1,a,b) ->
                                         let uu____9072 = aux NBE_t [] bs2
                                            in
                                         (match uu____9072 with
                                          | (w',uu____9106,uu____9107) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____9167 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____9167 msg);
                                FStar_Pervasives_Native.None))))
  