open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____63793  ->
    let uu____63794 = FStar_Options.codegen ()  in
    uu____63794 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____63863 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____63893) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____63899) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____63904 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____63908 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_63922  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_63925 ->
          let uu____63926 =
            let uu____63928 = FStar_Range.string_of_range p  in
            let uu____63930 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____63928 uu____63930
             in
          failwith uu____63926
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____63947 =
        let uu____63948 =
          let uu____63949 =
            let uu____63961 = FStar_Util.string_of_int i  in
            (uu____63961, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____63949  in
        FStar_All.pipe_right uu____63948
          (fun _63974  -> FStar_Extraction_ML_Syntax.MLE_Const _63974)
         in
      FStar_All.pipe_right uu____63947
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____63983 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _63984  -> FStar_Extraction_ML_Syntax.MLE_Const _63984)
         in
      FStar_All.pipe_right uu____63983
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____63985 =
      let uu____63992 =
        let uu____63995 =
          let uu____63996 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____63996 cstr  in
        let uu____63999 =
          let uu____64002 =
            let uu____64003 =
              let uu____64005 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____64005 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____64003 cint  in
          let uu____64008 =
            let uu____64011 =
              let uu____64012 =
                let uu____64014 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____64014 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____64012 cint  in
            let uu____64017 =
              let uu____64020 =
                let uu____64021 =
                  let uu____64023 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____64023 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____64021 cint  in
              let uu____64026 =
                let uu____64029 =
                  let uu____64030 =
                    let uu____64032 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____64032 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____64030 cint  in
                [uu____64029]  in
              uu____64020 :: uu____64026  in
            uu____64011 :: uu____64017  in
          uu____64002 :: uu____64008  in
        uu____63995 :: uu____63999  in
      (mk_range_mle, uu____63992)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____63985
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____64049 ->
          let uu____64050 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____64050
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____64078 =
            FStar_Util.find_opt
              (fun uu____64094  ->
                 match uu____64094 with | (y,uu____64102) -> y = x) subst1
             in
          (match uu____64078 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____64126 =
            let uu____64133 = subst_aux subst1 t1  in
            let uu____64134 = subst_aux subst1 t2  in
            (uu____64133, f, uu____64134)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____64126
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____64141 =
            let uu____64148 = FStar_List.map (subst_aux subst1) args  in
            (uu____64148, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____64141
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____64156 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____64156
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____64172  ->
    fun args  ->
      match uu____64172 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____64186 =
               let uu____64187 = FStar_List.zip formals args  in
               subst_aux uu____64187 t  in
             FStar_Pervasives_Native.Some uu____64186)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____64219 = try_subst ts args  in
      match uu____64219 with
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
    fun uu___617_64236  ->
      match uu___617_64236 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____64245 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____64245 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____64251 = try_subst ts args  in
               (match uu____64251 with
                | FStar_Pervasives_Native.None  ->
                    let uu____64256 =
                      let uu____64258 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____64260 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____64262 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____64258 uu____64260 uu____64262
                       in
                    failwith uu____64256
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____64269 -> FStar_Pervasives_Native.None)
      | uu____64272 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____64286) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____64290 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_64302  ->
    match uu___618_64302 with
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
        | uu____64323 ->
            let uu____64328 =
              let uu____64330 = FStar_Range.string_of_range r  in
              let uu____64332 = eff_to_string f  in
              let uu____64334 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____64330
                uu____64332 uu____64334
               in
            failwith uu____64328
  
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
    (fun uu____64377  ->
       fun t  ->
         match uu____64377 with
         | (uu____64384,t0) ->
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
                | uu____64507 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____64544 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____64552 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____64552 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____64563;
                     FStar_Extraction_ML_Syntax.loc = uu____64564;_}
                   ->
                   let uu____64589 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____64589
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____64607 = type_leq unfold_ty t2 t2'  in
                        (if uu____64607
                         then
                           let body1 =
                             let uu____64618 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____64618
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____64623 =
                             let uu____64626 =
                               let uu____64627 =
                                 let uu____64632 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____64632
                                  in
                               FStar_All.pipe_left uu____64627
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____64626  in
                           (true, uu____64623)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____64672 =
                           let uu____64680 =
                             let uu____64683 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _64686  ->
                                  FStar_Pervasives_Native.Some _64686)
                               uu____64683
                              in
                           type_leq_c unfold_ty uu____64680 t2 t2'  in
                         match uu____64672 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____64708 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____64708
                               | uu____64719 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____64731 ->
                   let uu____64734 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____64734
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____64774 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____64774
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____64796 = unfold_ty t  in
                 match uu____64796 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____64807 = unfold_ty t'  in
                     (match uu____64807 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____64828 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____64828
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____64852,uu____64853)
              ->
              let uu____64860 = unfold_ty t  in
              (match uu____64860 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____64871 -> (false, FStar_Pervasives_Native.None))
          | (uu____64878,FStar_Extraction_ML_Syntax.MLTY_Named uu____64879)
              ->
              let uu____64886 = unfold_ty t'  in
              (match uu____64886 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____64897 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____64908 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____64922 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____64922 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____64950 =
          let uu____64957 = erase_effect_annotations t1  in
          let uu____64958 = erase_effect_annotations t2  in
          (uu____64957, FStar_Extraction_ML_Syntax.E_PURE, uu____64958)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____64950
    | uu____64959 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_64987  ->
    match uu___619_64987 with
    | (FStar_Util.Inl uu____64999,uu____65000)::uu____65001 -> true
    | uu____65025 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____65053  ->
    match uu____65053 with
    | (ns,n1) ->
        let uu____65075 =
          let uu____65077 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____65077  in
        if uu____65075
        then
          let uu____65087 =
            let uu____65089 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____65089  in
          FStar_Pervasives_Native.Some uu____65087
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____65108 = is_xtuple mlp  in
        (match uu____65108 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____65115 -> e)
    | uu____65119 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_65130  ->
    match uu___620_65130 with
    | f::uu____65137 ->
        let uu____65140 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____65140 with
         | (ns,uu____65151) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____65164 -> failwith "impos"
  
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
  fun uu____65230  ->
    match uu____65230 with
    | (ns,n1) ->
        let uu____65252 =
          let uu____65254 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____65254  in
        if uu____65252
        then
          let uu____65264 =
            let uu____65266 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____65266  in
          FStar_Pervasives_Native.Some uu____65264
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____65285 = is_xtuple_ty mlp  in
        (match uu____65285 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____65292 -> t)
    | uu____65296 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____65310 = codegen_fsharp ()  in
    if uu____65310
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____65332  ->
    match uu____65332 with
    | (ns,n1) ->
        let uu____65352 = codegen_fsharp ()  in
        if uu____65352
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____65380 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____65380, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____65411 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____65411
      then true
      else
        (let uu____65418 = unfold_ty t  in
         match uu____65418 with
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
            let uu____65441 =
              let uu____65448 = eraseTypeDeep unfold_ty tyd  in
              let uu____65449 = eraseTypeDeep unfold_ty tycd  in
              (uu____65448, etag, uu____65449)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____65441
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____65458 = erasableType unfold_ty t  in
          if uu____65458
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____65463 =
               let uu____65470 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____65470, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____65463)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____65478 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____65478
      | uu____65481 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____65492 =
    let uu____65497 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____65497  in
  FStar_All.pipe_left uu____65492
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
          let uu____65585 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____65585
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____65601 = FStar_Range.file_of_range r  in (line, uu____65601)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____65624,b) ->
        let uu____65626 = doms_and_cod b  in
        (match uu____65626 with | (ds,c) -> ((a :: ds), c))
    | uu____65647 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____65660 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____65660
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____65688,b) ->
        let uu____65690 = uncurry_mlty_fun b  in
        (match uu____65690 with | (args,res) -> ((a :: args), res))
    | uu____65711 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____65727 -> true
    | uu____65730 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____65741 -> uu____65741
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____65763 =
          let uu____65769 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____65769)  in
        FStar_Errors.log_issue r uu____65763
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____65782 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____65793 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____65804 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____65815 -> false
  
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
              let uu____65886 =
                let uu____65887 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65887  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65886
               in
            let lid_to_top_name l =
              let uu____65894 =
                let uu____65895 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65895  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65894
               in
            let str_to_name s =
              let uu____65904 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____65904  in
            let str_to_top_name s =
              let uu____65913 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____65913  in
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
              let uu____65951 =
                let uu____65952 =
                  let uu____65959 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____65961 =
                    let uu____65964 =
                      let uu____65965 =
                        let uu____65966 =
                          let uu____65967 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____65967
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____65966  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____65965
                       in
                    [uu____65964]  in
                  (uu____65959, uu____65961)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65952  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65951
               in
            let emb_prefix uu___621_65982 =
              match uu___621_65982 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____65996 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____66007 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____66036 =
                let uu____66038 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____66038  in
              emb_prefix l uu____66036  in
            let mk_any_embedding l s =
              let uu____66054 =
                let uu____66055 =
                  let uu____66062 = emb_prefix l "mk_any_emb"  in
                  let uu____66064 =
                    let uu____66067 = str_to_name s  in [uu____66067]  in
                  (uu____66062, uu____66064)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____66055  in
              FStar_All.pipe_left w uu____66054  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____66117 =
                let uu____66118 =
                  let uu____66125 = emb_prefix l "e_arrow"  in
                  (uu____66125, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____66118  in
              FStar_All.pipe_left w uu____66117  in
            let known_type_constructors =
              let term_cs =
                let uu____66163 =
                  let uu____66178 =
                    let uu____66193 =
                      let uu____66208 =
                        let uu____66223 =
                          let uu____66238 =
                            let uu____66253 =
                              let uu____66268 =
                                let uu____66281 =
                                  let uu____66290 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____66290, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____66281, Syntax_term)  in
                              let uu____66304 =
                                let uu____66319 =
                                  let uu____66332 =
                                    let uu____66341 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____66341, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____66332, Refl_emb)  in
                                let uu____66355 =
                                  let uu____66370 =
                                    let uu____66383 =
                                      let uu____66392 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____66392, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____66383, Refl_emb)  in
                                  let uu____66406 =
                                    let uu____66421 =
                                      let uu____66434 =
                                        let uu____66443 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____66443, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____66434, Refl_emb)  in
                                    let uu____66457 =
                                      let uu____66472 =
                                        let uu____66485 =
                                          let uu____66494 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____66494,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____66485, Refl_emb)  in
                                      let uu____66508 =
                                        let uu____66523 =
                                          let uu____66536 =
                                            let uu____66545 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____66545,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____66536, Refl_emb)  in
                                        [uu____66523]  in
                                      uu____66472 :: uu____66508  in
                                    uu____66421 :: uu____66457  in
                                  uu____66370 :: uu____66406  in
                                uu____66319 :: uu____66355  in
                              uu____66268 :: uu____66304  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____66253
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____66238
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____66223
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____66208
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____66193
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____66178
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____66163
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_66852  ->
                     match uu___622_66852 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____66927 -> failwith "Impossible") term_cs
                 in
              fun uu___623_66953  ->
                match uu___623_66953 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____66968 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____67005  ->
                   match uu____67005 with
                   | ((x,args,uu____67021),uu____67022) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____67052 =
              match uu____67052 with
              | (bv',uu____67060) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____67094 =
                let uu____67095 = FStar_Syntax_Subst.compress t3  in
                uu____67095.FStar_Syntax_Syntax.n  in
              match uu____67094 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____67104 =
                    let uu____67106 =
                      let uu____67112 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____67112  in
                    FStar_Pervasives_Native.snd uu____67106  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____67104
              | FStar_Syntax_Syntax.Tm_refine (x,uu____67133) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____67139,uu____67140)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____67213 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____67213 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____67235 =
                           let uu____67236 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____67236  in
                         uu____67235.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____67254 = mk_embedding l env t0  in
                       let uu____67255 = mk_embedding l env t11  in
                       emb_arrow l uu____67254 uu____67255)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____67326 =
                      let uu____67333 =
                        let uu____67334 =
                          let uu____67349 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____67349)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____67334  in
                      FStar_Syntax_Syntax.mk uu____67333  in
                    uu____67326 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____67374 ->
                  let uu____67375 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____67375 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____67427 =
                         let uu____67428 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____67428.FStar_Syntax_Syntax.n  in
                       (match uu____67427 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____67454  ->
                                      match uu____67454 with
                                      | (t4,uu____67462) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____67469 =
                              let uu____67482 =
                                FStar_Util.find_opt
                                  (fun uu____67514  ->
                                     match uu____67514 with
                                     | ((x,uu____67529,uu____67530),uu____67531)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____67482
                                FStar_Util.must
                               in
                            (match uu____67469 with
                             | ((uu____67582,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67599 when
                                      _67599 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67604 ->
                            let uu____67605 =
                              let uu____67606 =
                                let uu____67608 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67608
                                 in
                              NoTacticEmbedding uu____67606  in
                            FStar_Exn.raise uu____67605))
              | FStar_Syntax_Syntax.Tm_uinst uu____67611 ->
                  let uu____67618 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____67618 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____67670 =
                         let uu____67671 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____67671.FStar_Syntax_Syntax.n  in
                       (match uu____67670 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____67697  ->
                                      match uu____67697 with
                                      | (t4,uu____67705) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____67712 =
                              let uu____67725 =
                                FStar_Util.find_opt
                                  (fun uu____67757  ->
                                     match uu____67757 with
                                     | ((x,uu____67772,uu____67773),uu____67774)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____67725
                                FStar_Util.must
                               in
                            (match uu____67712 with
                             | ((uu____67825,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67842 when
                                      _67842 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67847 ->
                            let uu____67848 =
                              let uu____67849 =
                                let uu____67851 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67851
                                 in
                              NoTacticEmbedding uu____67849  in
                            FStar_Exn.raise uu____67848))
              | FStar_Syntax_Syntax.Tm_app uu____67854 ->
                  let uu____67871 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____67871 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____67923 =
                         let uu____67924 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____67924.FStar_Syntax_Syntax.n  in
                       (match uu____67923 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____67950  ->
                                      match uu____67950 with
                                      | (t4,uu____67958) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____67965 =
                              let uu____67978 =
                                FStar_Util.find_opt
                                  (fun uu____68010  ->
                                     match uu____68010 with
                                     | ((x,uu____68025,uu____68026),uu____68027)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____67978
                                FStar_Util.must
                               in
                            (match uu____67965 with
                             | ((uu____68078,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _68095 when
                                      _68095 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____68100 ->
                            let uu____68101 =
                              let uu____68102 =
                                let uu____68104 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____68104
                                 in
                              NoTacticEmbedding uu____68102  in
                            FStar_Exn.raise uu____68101))
              | uu____68107 ->
                  let uu____68108 =
                    let uu____68109 =
                      let uu____68111 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____68111
                       in
                    NoTacticEmbedding uu____68109  in
                  FStar_Exn.raise uu____68108
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____68133 =
                      let uu____68134 =
                        let uu____68141 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____68143 =
                          let uu____68146 =
                            let uu____68147 =
                              let uu____68148 =
                                let uu____68149 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____68149
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____68148
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____68147
                             in
                          let uu____68151 =
                            let uu____68154 =
                              let uu____68155 =
                                let uu____68156 =
                                  let uu____68157 =
                                    let uu____68164 =
                                      let uu____68167 = str_to_name "args"
                                         in
                                      [uu____68167]  in
                                    (body, uu____68164)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____68157
                                   in
                                FStar_All.pipe_left w uu____68156  in
                              mk_lam "_" uu____68155  in
                            [uu____68154]  in
                          uu____68146 :: uu____68151  in
                        (uu____68141, uu____68143)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____68134  in
                    FStar_All.pipe_left w uu____68133  in
                  mk_lam "args" body1
              | uu____68175 ->
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
                    let uu____68224 =
                      let uu____68225 =
                        let uu____68226 =
                          let uu____68233 =
                            let uu____68236 = str_to_name "args"  in
                            [uu____68236]  in
                          (body, uu____68233)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____68226  in
                      FStar_All.pipe_left w uu____68225  in
                    (pattern, FStar_Pervasives_Native.None, uu____68224)  in
                  let default_branch =
                    let uu____68251 =
                      let uu____68252 =
                        let uu____68253 =
                          let uu____68260 = str_to_name "failwith"  in
                          let uu____68262 =
                            let uu____68265 =
                              let uu____68266 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____68266  in
                            [uu____68265]  in
                          (uu____68260, uu____68262)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____68253  in
                      FStar_All.pipe_left w uu____68252  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____68251)
                     in
                  let body1 =
                    let uu____68274 =
                      let uu____68275 =
                        let uu____68290 = str_to_name "args"  in
                        (uu____68290, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____68275  in
                    FStar_All.pipe_left w uu____68274  in
                  let body2 =
                    let uu____68327 =
                      let uu____68328 =
                        let uu____68335 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____68337 =
                          let uu____68340 =
                            let uu____68341 =
                              let uu____68342 =
                                let uu____68343 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____68343
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____68342
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____68341
                             in
                          let uu____68345 =
                            let uu____68348 = mk_lam "_" body1  in
                            [uu____68348]  in
                          uu____68340 :: uu____68345  in
                        (uu____68335, uu____68337)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____68328  in
                    FStar_All.pipe_left w uu____68327  in
                  mk_lam "args" body2
               in
            let uu____68353 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____68353 with
            | (bs,c) ->
                let uu____68386 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____68479 = FStar_Util.first_N n1 bs  in
                           match uu____68479 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____68557 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____68557
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____68574 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____68576 = FStar_Util.string_of_int n1
                                in
                             let uu____68578 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____68574 uu____68576 uu____68578
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____68386 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____68629 =
                       let uu____68650 =
                         FStar_Util.prefix_until
                           (fun uu____68692  ->
                              match uu____68692 with
                              | (b,uu____68701) ->
                                  let uu____68706 =
                                    let uu____68707 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____68707.FStar_Syntax_Syntax.n  in
                                  (match uu____68706 with
                                   | FStar_Syntax_Syntax.Tm_type uu____68711
                                       -> false
                                   | uu____68713 -> true)) bs1
                          in
                       match uu____68650 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____68629 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____68955 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____68955) type_vars
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
                                let uu____69055 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____69055
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____69072 =
                                      let uu____69075 =
                                        let uu____69078 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____69079 =
                                          let uu____69082 =
                                            let uu____69083 =
                                              let uu____69084 =
                                                let uu____69085 =
                                                  let uu____69097 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____69097,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____69085
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____69084
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____69083
                                             in
                                          [uu____69082; fv_lid_embedded; cb]
                                           in
                                        uu____69078 :: uu____69079  in
                                      res_embedding :: uu____69075  in
                                    FStar_List.append arg_unembeddings
                                      uu____69072
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
                                  let uu____69116 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____69116, arity, true)
                                else
                                  (let uu____69126 =
                                     let uu____69128 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____69128
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____69126
                                   then
                                     let h =
                                       let uu____69139 =
                                         let uu____69141 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____69141
                                          in
                                       str_to_top_name uu____69139  in
                                     let tac_fun =
                                       let uu____69144 =
                                         let uu____69145 =
                                           let uu____69152 =
                                             let uu____69153 =
                                               let uu____69155 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____69155
                                                in
                                             str_to_top_name uu____69153  in
                                           let uu____69157 =
                                             let uu____69160 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____69160]  in
                                           (uu____69152, uu____69157)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____69145
                                          in
                                       FStar_All.pipe_left w uu____69144  in
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
                                           let uu____69174 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____69174
                                       | uu____69178 ->
                                           let uu____69182 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____69182
                                        in
                                     let uu____69185 =
                                       let uu____69186 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____69186  in
                                     (uu____69185,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____69195 =
                                        let uu____69196 =
                                          let uu____69198 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____69198
                                           in
                                        NoTacticEmbedding uu____69196  in
                                      FStar_Exn.raise uu____69195))
                            | (b,uu____69210)::bs4 ->
                                let uu____69230 =
                                  let uu____69233 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____69233 :: accum_embeddings  in
                                aux loc uu____69230 bs4
                             in
                          (try
                             (fun uu___1304_69255  ->
                                match () with
                                | () ->
                                    let uu____69268 = aux Syntax_term [] bs2
                                       in
                                    (match uu____69268 with
                                     | (w1,a,b) ->
                                         let uu____69296 = aux NBE_t [] bs2
                                            in
                                         (match uu____69296 with
                                          | (w',uu____69318,uu____69319) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____69355 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____69355 msg);
                                FStar_Pervasives_Native.None))))
  