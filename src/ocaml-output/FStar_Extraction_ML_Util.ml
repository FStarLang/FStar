open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____62973  ->
    let uu____62974 = FStar_Options.codegen ()  in
    uu____62974 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____63043 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____63073) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____63079) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____63084 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____63088 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_63102  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_63105 ->
          let uu____63106 =
            let uu____63108 = FStar_Range.string_of_range p  in
            let uu____63110 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____63108 uu____63110
             in
          failwith uu____63106
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____63127 =
        let uu____63128 =
          let uu____63129 =
            let uu____63141 = FStar_Util.string_of_int i  in
            (uu____63141, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____63129  in
        FStar_All.pipe_right uu____63128
          (fun _63154  -> FStar_Extraction_ML_Syntax.MLE_Const _63154)
         in
      FStar_All.pipe_right uu____63127
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____63163 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _63164  -> FStar_Extraction_ML_Syntax.MLE_Const _63164)
         in
      FStar_All.pipe_right uu____63163
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____63165 =
      let uu____63172 =
        let uu____63175 =
          let uu____63176 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____63176 cstr  in
        let uu____63179 =
          let uu____63182 =
            let uu____63183 =
              let uu____63185 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____63185 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____63183 cint  in
          let uu____63188 =
            let uu____63191 =
              let uu____63192 =
                let uu____63194 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____63194 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____63192 cint  in
            let uu____63197 =
              let uu____63200 =
                let uu____63201 =
                  let uu____63203 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____63203 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____63201 cint  in
              let uu____63206 =
                let uu____63209 =
                  let uu____63210 =
                    let uu____63212 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____63212 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____63210 cint  in
                [uu____63209]  in
              uu____63200 :: uu____63206  in
            uu____63191 :: uu____63197  in
          uu____63182 :: uu____63188  in
        uu____63175 :: uu____63179  in
      (mk_range_mle, uu____63172)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____63165
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____63229 ->
          let uu____63230 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____63230
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____63258 =
            FStar_Util.find_opt
              (fun uu____63274  ->
                 match uu____63274 with | (y,uu____63282) -> y = x) subst1
             in
          (match uu____63258 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____63306 =
            let uu____63313 = subst_aux subst1 t1  in
            let uu____63314 = subst_aux subst1 t2  in
            (uu____63313, f, uu____63314)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____63306
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____63321 =
            let uu____63328 = FStar_List.map (subst_aux subst1) args  in
            (uu____63328, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____63321
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____63336 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____63336
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____63352  ->
    fun args  ->
      match uu____63352 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____63366 =
               let uu____63367 = FStar_List.zip formals args  in
               subst_aux uu____63367 t  in
             FStar_Pervasives_Native.Some uu____63366)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____63399 = try_subst ts args  in
      match uu____63399 with
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
    fun uu___617_63416  ->
      match uu___617_63416 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____63425 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____63425 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____63431 = try_subst ts args  in
               (match uu____63431 with
                | FStar_Pervasives_Native.None  ->
                    let uu____63436 =
                      let uu____63438 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____63440 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____63442 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____63438 uu____63440 uu____63442
                       in
                    failwith uu____63436
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____63449 -> FStar_Pervasives_Native.None)
      | uu____63452 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____63466) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____63470 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_63482  ->
    match uu___618_63482 with
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
        | uu____63503 ->
            let uu____63508 =
              let uu____63510 = FStar_Range.string_of_range r  in
              let uu____63512 = eff_to_string f  in
              let uu____63514 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____63510
                uu____63512 uu____63514
               in
            failwith uu____63508
  
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
    (fun uu____63557  ->
       fun t  ->
         match uu____63557 with
         | (uu____63564,t0) ->
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
                | uu____63687 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____63724 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____63732 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____63732 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____63743;
                     FStar_Extraction_ML_Syntax.loc = uu____63744;_}
                   ->
                   let uu____63769 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____63769
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____63787 = type_leq unfold_ty t2 t2'  in
                        (if uu____63787
                         then
                           let body1 =
                             let uu____63798 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____63798
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____63803 =
                             let uu____63806 =
                               let uu____63807 =
                                 let uu____63812 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____63812
                                  in
                               FStar_All.pipe_left uu____63807
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____63806  in
                           (true, uu____63803)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____63852 =
                           let uu____63860 =
                             let uu____63863 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _63866  ->
                                  FStar_Pervasives_Native.Some _63866)
                               uu____63863
                              in
                           type_leq_c unfold_ty uu____63860 t2 t2'  in
                         match uu____63852 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____63888 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____63888
                               | uu____63899 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____63911 ->
                   let uu____63914 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____63914
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____63954 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____63954
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____63976 = unfold_ty t  in
                 match uu____63976 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____63987 = unfold_ty t'  in
                     (match uu____63987 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____64008 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____64008
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____64032,uu____64033)
              ->
              let uu____64040 = unfold_ty t  in
              (match uu____64040 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____64051 -> (false, FStar_Pervasives_Native.None))
          | (uu____64058,FStar_Extraction_ML_Syntax.MLTY_Named uu____64059)
              ->
              let uu____64066 = unfold_ty t'  in
              (match uu____64066 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____64077 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____64088 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____64102 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____64102 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____64130 =
          let uu____64137 = erase_effect_annotations t1  in
          let uu____64138 = erase_effect_annotations t2  in
          (uu____64137, FStar_Extraction_ML_Syntax.E_PURE, uu____64138)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____64130
    | uu____64139 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_64167  ->
    match uu___619_64167 with
    | (FStar_Util.Inl uu____64179,uu____64180)::uu____64181 -> true
    | uu____64205 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____64233  ->
    match uu____64233 with
    | (ns,n1) ->
        let uu____64255 =
          let uu____64257 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____64257  in
        if uu____64255
        then
          let uu____64267 =
            let uu____64269 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____64269  in
          FStar_Pervasives_Native.Some uu____64267
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____64288 = is_xtuple mlp  in
        (match uu____64288 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____64295 -> e)
    | uu____64299 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_64310  ->
    match uu___620_64310 with
    | f::uu____64317 ->
        let uu____64320 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____64320 with
         | (ns,uu____64331) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____64344 -> failwith "impos"
  
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
  fun uu____64410  ->
    match uu____64410 with
    | (ns,n1) ->
        let uu____64432 =
          let uu____64434 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____64434  in
        if uu____64432
        then
          let uu____64444 =
            let uu____64446 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____64446  in
          FStar_Pervasives_Native.Some uu____64444
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____64465 = is_xtuple_ty mlp  in
        (match uu____64465 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____64472 -> t)
    | uu____64476 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____64490 = codegen_fsharp ()  in
    if uu____64490
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____64512  ->
    match uu____64512 with
    | (ns,n1) ->
        let uu____64532 = codegen_fsharp ()  in
        if uu____64532
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____64560 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____64560, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____64591 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____64591
      then true
      else
        (let uu____64598 = unfold_ty t  in
         match uu____64598 with
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
            let uu____64621 =
              let uu____64628 = eraseTypeDeep unfold_ty tyd  in
              let uu____64629 = eraseTypeDeep unfold_ty tycd  in
              (uu____64628, etag, uu____64629)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____64621
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____64638 = erasableType unfold_ty t  in
          if uu____64638
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____64643 =
               let uu____64650 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____64650, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____64643)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____64658 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____64658
      | uu____64661 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____64672 =
    let uu____64677 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____64677  in
  FStar_All.pipe_left uu____64672
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
          let uu____64765 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____64765
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____64781 = FStar_Range.file_of_range r  in (line, uu____64781)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64804,b) ->
        let uu____64806 = doms_and_cod b  in
        (match uu____64806 with | (ds,c) -> ((a :: ds), c))
    | uu____64827 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____64840 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____64840
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64868,b) ->
        let uu____64870 = uncurry_mlty_fun b  in
        (match uu____64870 with | (args,res) -> ((a :: args), res))
    | uu____64891 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____64907 -> true
    | uu____64910 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____64920 -> uu____64920
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____64942 =
          let uu____64948 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____64948)  in
        FStar_Errors.log_issue r uu____64942
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____64961 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____64972 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____64983 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____64994 -> false
  
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
              let uu____65065 =
                let uu____65066 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65066  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65065
               in
            let lid_to_top_name l =
              let uu____65073 =
                let uu____65074 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65074  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65073
               in
            let str_to_name s =
              let uu____65083 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____65083  in
            let str_to_top_name s =
              let uu____65092 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____65092  in
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
              let uu____65130 =
                let uu____65131 =
                  let uu____65138 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____65140 =
                    let uu____65143 =
                      let uu____65144 =
                        let uu____65145 =
                          let uu____65146 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____65146
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____65145  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____65144
                       in
                    [uu____65143]  in
                  (uu____65138, uu____65140)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65131  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65130
               in
            let emb_prefix uu___621_65161 =
              match uu___621_65161 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____65175 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____65186 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____65215 =
                let uu____65217 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____65217  in
              emb_prefix l uu____65215  in
            let mk_any_embedding l s =
              let uu____65233 =
                let uu____65234 =
                  let uu____65241 = emb_prefix l "mk_any_emb"  in
                  let uu____65243 =
                    let uu____65246 = str_to_name s  in [uu____65246]  in
                  (uu____65241, uu____65243)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65234  in
              FStar_All.pipe_left w uu____65233  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____65296 =
                let uu____65297 =
                  let uu____65304 = emb_prefix l "e_arrow"  in
                  (uu____65304, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65297  in
              FStar_All.pipe_left w uu____65296  in
            let known_type_constructors =
              let term_cs =
                let uu____65342 =
                  let uu____65357 =
                    let uu____65372 =
                      let uu____65387 =
                        let uu____65402 =
                          let uu____65417 =
                            let uu____65432 =
                              let uu____65447 =
                                let uu____65460 =
                                  let uu____65469 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____65469, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____65460, Syntax_term)  in
                              let uu____65483 =
                                let uu____65498 =
                                  let uu____65511 =
                                    let uu____65520 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____65520, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____65511, Refl_emb)  in
                                let uu____65534 =
                                  let uu____65549 =
                                    let uu____65562 =
                                      let uu____65571 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____65571, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____65562, Refl_emb)  in
                                  let uu____65585 =
                                    let uu____65600 =
                                      let uu____65613 =
                                        let uu____65622 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____65622, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____65613, Refl_emb)  in
                                    let uu____65636 =
                                      let uu____65651 =
                                        let uu____65664 =
                                          let uu____65673 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____65673,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____65664, Refl_emb)  in
                                      let uu____65687 =
                                        let uu____65702 =
                                          let uu____65715 =
                                            let uu____65724 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____65724,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____65715, Refl_emb)  in
                                        [uu____65702]  in
                                      uu____65651 :: uu____65687  in
                                    uu____65600 :: uu____65636  in
                                  uu____65549 :: uu____65585  in
                                uu____65498 :: uu____65534  in
                              uu____65447 :: uu____65483  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____65432
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____65417
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____65402
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____65387
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____65372
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____65357
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____65342
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_66031  ->
                     match uu___622_66031 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____66106 -> failwith "Impossible") term_cs
                 in
              fun uu___623_66132  ->
                match uu___623_66132 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____66147 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____66184  ->
                   match uu____66184 with
                   | ((x,args,uu____66200),uu____66201) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____66231 =
              match uu____66231 with
              | (bv',uu____66239) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____66273 =
                let uu____66274 = FStar_Syntax_Subst.compress t3  in
                uu____66274.FStar_Syntax_Syntax.n  in
              match uu____66273 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____66283 =
                    let uu____66285 =
                      let uu____66291 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____66291  in
                    FStar_Pervasives_Native.snd uu____66285  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____66283
              | FStar_Syntax_Syntax.Tm_refine (x,uu____66312) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____66318,uu____66319)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____66392 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____66392 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____66414 =
                           let uu____66415 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____66415  in
                         uu____66414.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____66433 = mk_embedding l env t0  in
                       let uu____66434 = mk_embedding l env t11  in
                       emb_arrow l uu____66433 uu____66434)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____66505 =
                      let uu____66512 =
                        let uu____66513 =
                          let uu____66528 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____66528)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____66513  in
                      FStar_Syntax_Syntax.mk uu____66512  in
                    uu____66505 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____66553 ->
                  let uu____66554 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66554 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66606 =
                         let uu____66607 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66607.FStar_Syntax_Syntax.n  in
                       (match uu____66606 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66633  ->
                                      match uu____66633 with
                                      | (t4,uu____66641) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66648 =
                              let uu____66661 =
                                FStar_Util.find_opt
                                  (fun uu____66693  ->
                                     match uu____66693 with
                                     | ((x,uu____66708,uu____66709),uu____66710)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66661
                                FStar_Util.must
                               in
                            (match uu____66648 with
                             | ((uu____66761,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _66778 when
                                      _66778 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____66783 ->
                            let uu____66784 =
                              let uu____66785 =
                                let uu____66787 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____66787
                                 in
                              NoTacticEmbedding uu____66785  in
                            FStar_Exn.raise uu____66784))
              | FStar_Syntax_Syntax.Tm_uinst uu____66790 ->
                  let uu____66797 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66797 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66849 =
                         let uu____66850 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66850.FStar_Syntax_Syntax.n  in
                       (match uu____66849 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66876  ->
                                      match uu____66876 with
                                      | (t4,uu____66884) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66891 =
                              let uu____66904 =
                                FStar_Util.find_opt
                                  (fun uu____66936  ->
                                     match uu____66936 with
                                     | ((x,uu____66951,uu____66952),uu____66953)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66904
                                FStar_Util.must
                               in
                            (match uu____66891 with
                             | ((uu____67004,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67021 when
                                      _67021 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67026 ->
                            let uu____67027 =
                              let uu____67028 =
                                let uu____67030 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67030
                                 in
                              NoTacticEmbedding uu____67028  in
                            FStar_Exn.raise uu____67027))
              | FStar_Syntax_Syntax.Tm_app uu____67033 ->
                  let uu____67050 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____67050 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____67102 =
                         let uu____67103 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____67103.FStar_Syntax_Syntax.n  in
                       (match uu____67102 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____67129  ->
                                      match uu____67129 with
                                      | (t4,uu____67137) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____67144 =
                              let uu____67157 =
                                FStar_Util.find_opt
                                  (fun uu____67189  ->
                                     match uu____67189 with
                                     | ((x,uu____67204,uu____67205),uu____67206)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____67157
                                FStar_Util.must
                               in
                            (match uu____67144 with
                             | ((uu____67257,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67274 when
                                      _67274 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67279 ->
                            let uu____67280 =
                              let uu____67281 =
                                let uu____67283 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67283
                                 in
                              NoTacticEmbedding uu____67281  in
                            FStar_Exn.raise uu____67280))
              | uu____67286 ->
                  let uu____67287 =
                    let uu____67288 =
                      let uu____67290 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____67290
                       in
                    NoTacticEmbedding uu____67288  in
                  FStar_Exn.raise uu____67287
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____67312 =
                      let uu____67313 =
                        let uu____67320 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67322 =
                          let uu____67325 =
                            let uu____67326 =
                              let uu____67327 =
                                let uu____67328 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67328
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67327
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67326
                             in
                          let uu____67330 =
                            let uu____67333 =
                              let uu____67334 =
                                let uu____67335 =
                                  let uu____67336 =
                                    let uu____67343 =
                                      let uu____67346 = str_to_name "args"
                                         in
                                      [uu____67346]  in
                                    (body, uu____67343)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____67336
                                   in
                                FStar_All.pipe_left w uu____67335  in
                              mk_lam "_" uu____67334  in
                            [uu____67333]  in
                          uu____67325 :: uu____67330  in
                        (uu____67320, uu____67322)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67313  in
                    FStar_All.pipe_left w uu____67312  in
                  mk_lam "args" body1
              | uu____67354 ->
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
                    let uu____67403 =
                      let uu____67404 =
                        let uu____67405 =
                          let uu____67412 =
                            let uu____67415 = str_to_name "args"  in
                            [uu____67415]  in
                          (body, uu____67412)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67405  in
                      FStar_All.pipe_left w uu____67404  in
                    (pattern, FStar_Pervasives_Native.None, uu____67403)  in
                  let default_branch =
                    let uu____67430 =
                      let uu____67431 =
                        let uu____67432 =
                          let uu____67439 = str_to_name "failwith"  in
                          let uu____67441 =
                            let uu____67444 =
                              let uu____67445 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____67445  in
                            [uu____67444]  in
                          (uu____67439, uu____67441)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67432  in
                      FStar_All.pipe_left w uu____67431  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____67430)
                     in
                  let body1 =
                    let uu____67453 =
                      let uu____67454 =
                        let uu____67469 = str_to_name "args"  in
                        (uu____67469, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____67454  in
                    FStar_All.pipe_left w uu____67453  in
                  let body2 =
                    let uu____67506 =
                      let uu____67507 =
                        let uu____67514 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67516 =
                          let uu____67519 =
                            let uu____67520 =
                              let uu____67521 =
                                let uu____67522 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67522
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67521
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67520
                             in
                          let uu____67524 =
                            let uu____67527 = mk_lam "_" body1  in
                            [uu____67527]  in
                          uu____67519 :: uu____67524  in
                        (uu____67514, uu____67516)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67507  in
                    FStar_All.pipe_left w uu____67506  in
                  mk_lam "args" body2
               in
            let uu____67532 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____67532 with
            | (bs,c) ->
                let uu____67565 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____67658 = FStar_Util.first_N n1 bs  in
                           match uu____67658 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____67736 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____67736
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____67753 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____67755 = FStar_Util.string_of_int n1
                                in
                             let uu____67757 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____67753 uu____67755 uu____67757
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____67565 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____67808 =
                       let uu____67829 =
                         FStar_Util.prefix_until
                           (fun uu____67871  ->
                              match uu____67871 with
                              | (b,uu____67880) ->
                                  let uu____67885 =
                                    let uu____67886 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____67886.FStar_Syntax_Syntax.n  in
                                  (match uu____67885 with
                                   | FStar_Syntax_Syntax.Tm_type uu____67890
                                       -> false
                                   | uu____67892 -> true)) bs1
                          in
                       match uu____67829 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____67808 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____68134 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____68134) type_vars
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
                                let uu____68234 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____68234
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____68251 =
                                      let uu____68254 =
                                        let uu____68257 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____68258 =
                                          let uu____68261 =
                                            let uu____68262 =
                                              let uu____68263 =
                                                let uu____68264 =
                                                  let uu____68276 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____68276,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____68264
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____68263
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____68262
                                             in
                                          [uu____68261; fv_lid_embedded; cb]
                                           in
                                        uu____68257 :: uu____68258  in
                                      res_embedding :: uu____68254  in
                                    FStar_List.append arg_unembeddings
                                      uu____68251
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
                                  let uu____68295 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____68295, arity, true)
                                else
                                  (let uu____68305 =
                                     let uu____68307 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____68307
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____68305
                                   then
                                     let h =
                                       let uu____68318 =
                                         let uu____68320 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____68320
                                          in
                                       str_to_top_name uu____68318  in
                                     let tac_fun =
                                       let uu____68323 =
                                         let uu____68324 =
                                           let uu____68331 =
                                             let uu____68332 =
                                               let uu____68334 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____68334
                                                in
                                             str_to_top_name uu____68332  in
                                           let uu____68336 =
                                             let uu____68339 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____68339]  in
                                           (uu____68331, uu____68336)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____68324
                                          in
                                       FStar_All.pipe_left w uu____68323  in
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
                                           let uu____68353 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____68353
                                       | uu____68357 ->
                                           let uu____68361 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____68361
                                        in
                                     let uu____68364 =
                                       let uu____68365 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____68365  in
                                     (uu____68364,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____68374 =
                                        let uu____68375 =
                                          let uu____68377 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____68377
                                           in
                                        NoTacticEmbedding uu____68375  in
                                      FStar_Exn.raise uu____68374))
                            | (b,uu____68389)::bs4 ->
                                let uu____68409 =
                                  let uu____68412 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____68412 :: accum_embeddings  in
                                aux loc uu____68409 bs4
                             in
                          (try
                             (fun uu___1304_68434  ->
                                match () with
                                | () ->
                                    let uu____68447 = aux Syntax_term [] bs2
                                       in
                                    (match uu____68447 with
                                     | (w1,a,b) ->
                                         let uu____68475 = aux NBE_t [] bs2
                                            in
                                         (match uu____68475 with
                                          | (w',uu____68497,uu____68498) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____68534 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____68534 msg);
                                FStar_Pervasives_Native.None))))
  