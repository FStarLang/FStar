open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____62954  ->
    let uu____62955 = FStar_Options.codegen ()  in
    uu____62955 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____63024 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____63054) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____63060) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____63065 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____63069 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_63083  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_63086 ->
          let uu____63087 =
            let uu____63089 = FStar_Range.string_of_range p  in
            let uu____63091 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____63089 uu____63091
             in
          failwith uu____63087
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____63108 =
        let uu____63109 =
          let uu____63110 =
            let uu____63122 = FStar_Util.string_of_int i  in
            (uu____63122, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____63110  in
        FStar_All.pipe_right uu____63109
          (fun _63135  -> FStar_Extraction_ML_Syntax.MLE_Const _63135)
         in
      FStar_All.pipe_right uu____63108
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____63144 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _63145  -> FStar_Extraction_ML_Syntax.MLE_Const _63145)
         in
      FStar_All.pipe_right uu____63144
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____63146 =
      let uu____63153 =
        let uu____63156 =
          let uu____63157 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____63157 cstr  in
        let uu____63160 =
          let uu____63163 =
            let uu____63164 =
              let uu____63166 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____63166 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____63164 cint  in
          let uu____63169 =
            let uu____63172 =
              let uu____63173 =
                let uu____63175 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____63175 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____63173 cint  in
            let uu____63178 =
              let uu____63181 =
                let uu____63182 =
                  let uu____63184 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____63184 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____63182 cint  in
              let uu____63187 =
                let uu____63190 =
                  let uu____63191 =
                    let uu____63193 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____63193 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____63191 cint  in
                [uu____63190]  in
              uu____63181 :: uu____63187  in
            uu____63172 :: uu____63178  in
          uu____63163 :: uu____63169  in
        uu____63156 :: uu____63160  in
      (mk_range_mle, uu____63153)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____63146
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____63210 ->
          let uu____63211 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____63211
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____63239 =
            FStar_Util.find_opt
              (fun uu____63255  ->
                 match uu____63255 with | (y,uu____63263) -> y = x) subst1
             in
          (match uu____63239 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____63287 =
            let uu____63294 = subst_aux subst1 t1  in
            let uu____63295 = subst_aux subst1 t2  in
            (uu____63294, f, uu____63295)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____63287
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____63302 =
            let uu____63309 = FStar_List.map (subst_aux subst1) args  in
            (uu____63309, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____63302
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____63317 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____63317
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____63333  ->
    fun args  ->
      match uu____63333 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____63347 =
               let uu____63348 = FStar_List.zip formals args  in
               subst_aux uu____63348 t  in
             FStar_Pervasives_Native.Some uu____63347)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____63380 = try_subst ts args  in
      match uu____63380 with
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
    fun uu___617_63397  ->
      match uu___617_63397 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____63406 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____63406 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____63412 = try_subst ts args  in
               (match uu____63412 with
                | FStar_Pervasives_Native.None  ->
                    let uu____63417 =
                      let uu____63419 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____63421 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____63423 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____63419 uu____63421 uu____63423
                       in
                    failwith uu____63417
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____63430 -> FStar_Pervasives_Native.None)
      | uu____63433 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____63447) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____63451 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_63463  ->
    match uu___618_63463 with
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
        | uu____63484 ->
            let uu____63489 =
              let uu____63491 = FStar_Range.string_of_range r  in
              let uu____63493 = eff_to_string f  in
              let uu____63495 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____63491
                uu____63493 uu____63495
               in
            failwith uu____63489
  
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
    (fun uu____63538  ->
       fun t  ->
         match uu____63538 with
         | (uu____63545,t0) ->
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
                | uu____63668 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____63705 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____63713 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____63713 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____63724;
                     FStar_Extraction_ML_Syntax.loc = uu____63725;_}
                   ->
                   let uu____63750 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____63750
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____63768 = type_leq unfold_ty t2 t2'  in
                        (if uu____63768
                         then
                           let body1 =
                             let uu____63779 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____63779
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____63784 =
                             let uu____63787 =
                               let uu____63788 =
                                 let uu____63793 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____63793
                                  in
                               FStar_All.pipe_left uu____63788
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____63787  in
                           (true, uu____63784)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____63833 =
                           let uu____63841 =
                             let uu____63844 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _63847  ->
                                  FStar_Pervasives_Native.Some _63847)
                               uu____63844
                              in
                           type_leq_c unfold_ty uu____63841 t2 t2'  in
                         match uu____63833 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____63869 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____63869
                               | uu____63880 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____63892 ->
                   let uu____63895 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____63895
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____63935 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____63935
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____63957 = unfold_ty t  in
                 match uu____63957 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____63968 = unfold_ty t'  in
                     (match uu____63968 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____63989 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____63989
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____64013,uu____64014)
              ->
              let uu____64021 = unfold_ty t  in
              (match uu____64021 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____64032 -> (false, FStar_Pervasives_Native.None))
          | (uu____64039,FStar_Extraction_ML_Syntax.MLTY_Named uu____64040)
              ->
              let uu____64047 = unfold_ty t'  in
              (match uu____64047 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____64058 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____64069 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____64083 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____64083 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____64111 =
          let uu____64118 = erase_effect_annotations t1  in
          let uu____64119 = erase_effect_annotations t2  in
          (uu____64118, FStar_Extraction_ML_Syntax.E_PURE, uu____64119)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____64111
    | uu____64120 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_64148  ->
    match uu___619_64148 with
    | (FStar_Util.Inl uu____64160,uu____64161)::uu____64162 -> true
    | uu____64186 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____64214  ->
    match uu____64214 with
    | (ns,n1) ->
        let uu____64236 =
          let uu____64238 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____64238  in
        if uu____64236
        then
          let uu____64248 =
            let uu____64250 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____64250  in
          FStar_Pervasives_Native.Some uu____64248
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____64269 = is_xtuple mlp  in
        (match uu____64269 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____64276 -> e)
    | uu____64280 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_64291  ->
    match uu___620_64291 with
    | f::uu____64298 ->
        let uu____64301 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____64301 with
         | (ns,uu____64312) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____64325 -> failwith "impos"
  
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
  fun uu____64391  ->
    match uu____64391 with
    | (ns,n1) ->
        let uu____64413 =
          let uu____64415 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____64415  in
        if uu____64413
        then
          let uu____64425 =
            let uu____64427 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____64427  in
          FStar_Pervasives_Native.Some uu____64425
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____64446 = is_xtuple_ty mlp  in
        (match uu____64446 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____64453 -> t)
    | uu____64457 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____64471 = codegen_fsharp ()  in
    if uu____64471
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____64493  ->
    match uu____64493 with
    | (ns,n1) ->
        let uu____64513 = codegen_fsharp ()  in
        if uu____64513
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____64541 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____64541, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____64572 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____64572
      then true
      else
        (let uu____64579 = unfold_ty t  in
         match uu____64579 with
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
            let uu____64602 =
              let uu____64609 = eraseTypeDeep unfold_ty tyd  in
              let uu____64610 = eraseTypeDeep unfold_ty tycd  in
              (uu____64609, etag, uu____64610)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____64602
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____64619 = erasableType unfold_ty t  in
          if uu____64619
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____64624 =
               let uu____64631 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____64631, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____64624)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____64639 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____64639
      | uu____64642 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____64653 =
    let uu____64658 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____64658  in
  FStar_All.pipe_left uu____64653
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
          let uu____64746 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____64746
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____64762 = FStar_Range.file_of_range r  in (line, uu____64762)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64785,b) ->
        let uu____64787 = doms_and_cod b  in
        (match uu____64787 with | (ds,c) -> ((a :: ds), c))
    | uu____64808 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____64821 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____64821
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64849,b) ->
        let uu____64851 = uncurry_mlty_fun b  in
        (match uu____64851 with | (args,res) -> ((a :: args), res))
    | uu____64872 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____64888 -> true
    | uu____64891 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____64901 -> uu____64901
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____64923 =
          let uu____64929 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____64929)  in
        FStar_Errors.log_issue r uu____64923
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____64942 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____64953 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____64964 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____64975 -> false
  
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
              let uu____65046 =
                let uu____65047 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65047  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65046
               in
            let lid_to_top_name l =
              let uu____65054 =
                let uu____65055 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65055  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65054
               in
            let str_to_name s =
              let uu____65064 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____65064  in
            let str_to_top_name s =
              let uu____65073 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____65073  in
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
              let uu____65111 =
                let uu____65112 =
                  let uu____65119 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____65121 =
                    let uu____65124 =
                      let uu____65125 =
                        let uu____65126 =
                          let uu____65127 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____65127
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____65126  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____65125
                       in
                    [uu____65124]  in
                  (uu____65119, uu____65121)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65112  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65111
               in
            let emb_prefix uu___621_65142 =
              match uu___621_65142 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____65156 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____65167 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____65196 =
                let uu____65198 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____65198  in
              emb_prefix l uu____65196  in
            let mk_any_embedding l s =
              let uu____65214 =
                let uu____65215 =
                  let uu____65222 = emb_prefix l "mk_any_emb"  in
                  let uu____65224 =
                    let uu____65227 = str_to_name s  in [uu____65227]  in
                  (uu____65222, uu____65224)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65215  in
              FStar_All.pipe_left w uu____65214  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____65277 =
                let uu____65278 =
                  let uu____65285 = emb_prefix l "e_arrow"  in
                  (uu____65285, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65278  in
              FStar_All.pipe_left w uu____65277  in
            let known_type_constructors =
              let term_cs =
                let uu____65323 =
                  let uu____65338 =
                    let uu____65353 =
                      let uu____65368 =
                        let uu____65383 =
                          let uu____65398 =
                            let uu____65413 =
                              let uu____65428 =
                                let uu____65441 =
                                  let uu____65450 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____65450, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____65441, Syntax_term)  in
                              let uu____65464 =
                                let uu____65479 =
                                  let uu____65492 =
                                    let uu____65501 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____65501, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____65492, Refl_emb)  in
                                let uu____65515 =
                                  let uu____65530 =
                                    let uu____65543 =
                                      let uu____65552 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____65552, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____65543, Refl_emb)  in
                                  let uu____65566 =
                                    let uu____65581 =
                                      let uu____65594 =
                                        let uu____65603 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____65603, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____65594, Refl_emb)  in
                                    let uu____65617 =
                                      let uu____65632 =
                                        let uu____65645 =
                                          let uu____65654 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____65654,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____65645, Refl_emb)  in
                                      let uu____65668 =
                                        let uu____65683 =
                                          let uu____65696 =
                                            let uu____65705 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____65705,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____65696, Refl_emb)  in
                                        [uu____65683]  in
                                      uu____65632 :: uu____65668  in
                                    uu____65581 :: uu____65617  in
                                  uu____65530 :: uu____65566  in
                                uu____65479 :: uu____65515  in
                              uu____65428 :: uu____65464  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____65413
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____65398
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____65383
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____65368
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____65353
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____65338
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____65323
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_66012  ->
                     match uu___622_66012 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____66087 -> failwith "Impossible") term_cs
                 in
              fun uu___623_66113  ->
                match uu___623_66113 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____66128 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____66165  ->
                   match uu____66165 with
                   | ((x,args,uu____66181),uu____66182) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____66212 =
              match uu____66212 with
              | (bv',uu____66220) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____66254 =
                let uu____66255 = FStar_Syntax_Subst.compress t3  in
                uu____66255.FStar_Syntax_Syntax.n  in
              match uu____66254 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____66264 =
                    let uu____66266 =
                      let uu____66272 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____66272  in
                    FStar_Pervasives_Native.snd uu____66266  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____66264
              | FStar_Syntax_Syntax.Tm_refine (x,uu____66293) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____66299,uu____66300)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____66373 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____66373 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____66395 =
                           let uu____66396 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____66396  in
                         uu____66395.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____66414 = mk_embedding l env t0  in
                       let uu____66415 = mk_embedding l env t11  in
                       emb_arrow l uu____66414 uu____66415)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____66486 =
                      let uu____66493 =
                        let uu____66494 =
                          let uu____66509 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____66509)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____66494  in
                      FStar_Syntax_Syntax.mk uu____66493  in
                    uu____66486 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____66534 ->
                  let uu____66535 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66535 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66587 =
                         let uu____66588 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66588.FStar_Syntax_Syntax.n  in
                       (match uu____66587 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66614  ->
                                      match uu____66614 with
                                      | (t4,uu____66622) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66629 =
                              let uu____66642 =
                                FStar_Util.find_opt
                                  (fun uu____66674  ->
                                     match uu____66674 with
                                     | ((x,uu____66689,uu____66690),uu____66691)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66642
                                FStar_Util.must
                               in
                            (match uu____66629 with
                             | ((uu____66742,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _66759 when
                                      _66759 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____66764 ->
                            let uu____66765 =
                              let uu____66766 =
                                let uu____66768 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____66768
                                 in
                              NoTacticEmbedding uu____66766  in
                            FStar_Exn.raise uu____66765))
              | FStar_Syntax_Syntax.Tm_uinst uu____66771 ->
                  let uu____66778 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66778 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66830 =
                         let uu____66831 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66831.FStar_Syntax_Syntax.n  in
                       (match uu____66830 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66857  ->
                                      match uu____66857 with
                                      | (t4,uu____66865) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66872 =
                              let uu____66885 =
                                FStar_Util.find_opt
                                  (fun uu____66917  ->
                                     match uu____66917 with
                                     | ((x,uu____66932,uu____66933),uu____66934)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66885
                                FStar_Util.must
                               in
                            (match uu____66872 with
                             | ((uu____66985,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67002 when
                                      _67002 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67007 ->
                            let uu____67008 =
                              let uu____67009 =
                                let uu____67011 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67011
                                 in
                              NoTacticEmbedding uu____67009  in
                            FStar_Exn.raise uu____67008))
              | FStar_Syntax_Syntax.Tm_app uu____67014 ->
                  let uu____67031 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____67031 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____67083 =
                         let uu____67084 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____67084.FStar_Syntax_Syntax.n  in
                       (match uu____67083 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____67110  ->
                                      match uu____67110 with
                                      | (t4,uu____67118) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____67125 =
                              let uu____67138 =
                                FStar_Util.find_opt
                                  (fun uu____67170  ->
                                     match uu____67170 with
                                     | ((x,uu____67185,uu____67186),uu____67187)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____67138
                                FStar_Util.must
                               in
                            (match uu____67125 with
                             | ((uu____67238,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67255 when
                                      _67255 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67260 ->
                            let uu____67261 =
                              let uu____67262 =
                                let uu____67264 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67264
                                 in
                              NoTacticEmbedding uu____67262  in
                            FStar_Exn.raise uu____67261))
              | uu____67267 ->
                  let uu____67268 =
                    let uu____67269 =
                      let uu____67271 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____67271
                       in
                    NoTacticEmbedding uu____67269  in
                  FStar_Exn.raise uu____67268
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____67293 =
                      let uu____67294 =
                        let uu____67301 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67303 =
                          let uu____67306 =
                            let uu____67307 =
                              let uu____67308 =
                                let uu____67309 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67309
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67308
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67307
                             in
                          let uu____67311 =
                            let uu____67314 =
                              let uu____67315 =
                                let uu____67316 =
                                  let uu____67317 =
                                    let uu____67324 =
                                      let uu____67327 = str_to_name "args"
                                         in
                                      [uu____67327]  in
                                    (body, uu____67324)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____67317
                                   in
                                FStar_All.pipe_left w uu____67316  in
                              mk_lam "_" uu____67315  in
                            [uu____67314]  in
                          uu____67306 :: uu____67311  in
                        (uu____67301, uu____67303)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67294  in
                    FStar_All.pipe_left w uu____67293  in
                  mk_lam "args" body1
              | uu____67335 ->
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
                    let uu____67384 =
                      let uu____67385 =
                        let uu____67386 =
                          let uu____67393 =
                            let uu____67396 = str_to_name "args"  in
                            [uu____67396]  in
                          (body, uu____67393)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67386  in
                      FStar_All.pipe_left w uu____67385  in
                    (pattern, FStar_Pervasives_Native.None, uu____67384)  in
                  let default_branch =
                    let uu____67411 =
                      let uu____67412 =
                        let uu____67413 =
                          let uu____67420 = str_to_name "failwith"  in
                          let uu____67422 =
                            let uu____67425 =
                              let uu____67426 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____67426  in
                            [uu____67425]  in
                          (uu____67420, uu____67422)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67413  in
                      FStar_All.pipe_left w uu____67412  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____67411)
                     in
                  let body1 =
                    let uu____67434 =
                      let uu____67435 =
                        let uu____67450 = str_to_name "args"  in
                        (uu____67450, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____67435  in
                    FStar_All.pipe_left w uu____67434  in
                  let body2 =
                    let uu____67487 =
                      let uu____67488 =
                        let uu____67495 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67497 =
                          let uu____67500 =
                            let uu____67501 =
                              let uu____67502 =
                                let uu____67503 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67503
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67502
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67501
                             in
                          let uu____67505 =
                            let uu____67508 = mk_lam "_" body1  in
                            [uu____67508]  in
                          uu____67500 :: uu____67505  in
                        (uu____67495, uu____67497)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67488  in
                    FStar_All.pipe_left w uu____67487  in
                  mk_lam "args" body2
               in
            let uu____67513 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____67513 with
            | (bs,c) ->
                let uu____67546 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____67639 = FStar_Util.first_N n1 bs  in
                           match uu____67639 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____67717 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____67717
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____67734 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____67736 = FStar_Util.string_of_int n1
                                in
                             let uu____67738 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____67734 uu____67736 uu____67738
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____67546 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____67789 =
                       let uu____67810 =
                         FStar_Util.prefix_until
                           (fun uu____67852  ->
                              match uu____67852 with
                              | (b,uu____67861) ->
                                  let uu____67866 =
                                    let uu____67867 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____67867.FStar_Syntax_Syntax.n  in
                                  (match uu____67866 with
                                   | FStar_Syntax_Syntax.Tm_type uu____67871
                                       -> false
                                   | uu____67873 -> true)) bs1
                          in
                       match uu____67810 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____67789 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____68115 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____68115) type_vars
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
                                let uu____68215 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____68215
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____68232 =
                                      let uu____68235 =
                                        let uu____68238 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____68239 =
                                          let uu____68242 =
                                            let uu____68243 =
                                              let uu____68244 =
                                                let uu____68245 =
                                                  let uu____68257 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____68257,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____68245
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____68244
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____68243
                                             in
                                          [uu____68242; fv_lid_embedded; cb]
                                           in
                                        uu____68238 :: uu____68239  in
                                      res_embedding :: uu____68235  in
                                    FStar_List.append arg_unembeddings
                                      uu____68232
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
                                  let uu____68276 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____68276, arity, true)
                                else
                                  (let uu____68286 =
                                     let uu____68288 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____68288
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____68286
                                   then
                                     let h =
                                       let uu____68299 =
                                         let uu____68301 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____68301
                                          in
                                       str_to_top_name uu____68299  in
                                     let tac_fun =
                                       let uu____68304 =
                                         let uu____68305 =
                                           let uu____68312 =
                                             let uu____68313 =
                                               let uu____68315 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____68315
                                                in
                                             str_to_top_name uu____68313  in
                                           let uu____68317 =
                                             let uu____68320 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____68320]  in
                                           (uu____68312, uu____68317)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____68305
                                          in
                                       FStar_All.pipe_left w uu____68304  in
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
                                           let uu____68334 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____68334
                                       | uu____68338 ->
                                           let uu____68342 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____68342
                                        in
                                     let uu____68345 =
                                       let uu____68346 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____68346  in
                                     (uu____68345,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____68355 =
                                        let uu____68356 =
                                          let uu____68358 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____68358
                                           in
                                        NoTacticEmbedding uu____68356  in
                                      FStar_Exn.raise uu____68355))
                            | (b,uu____68370)::bs4 ->
                                let uu____68390 =
                                  let uu____68393 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____68393 :: accum_embeddings  in
                                aux loc uu____68390 bs4
                             in
                          (try
                             (fun uu___1304_68415  ->
                                match () with
                                | () ->
                                    let uu____68428 = aux Syntax_term [] bs2
                                       in
                                    (match uu____68428 with
                                     | (w1,a,b) ->
                                         let uu____68456 = aux NBE_t [] bs2
                                            in
                                         (match uu____68456 with
                                          | (w',uu____68478,uu____68479) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____68515 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____68515 msg);
                                FStar_Pervasives_Native.None))))
  