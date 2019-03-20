open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____62974  ->
    let uu____62975 = FStar_Options.codegen ()  in
    uu____62975 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____63044 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____63074) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____63080) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____63085 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____63089 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_63103  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_63106 ->
          let uu____63107 =
            let uu____63109 = FStar_Range.string_of_range p  in
            let uu____63111 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____63109 uu____63111
             in
          failwith uu____63107
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____63128 =
        let uu____63129 =
          let uu____63130 =
            let uu____63142 = FStar_Util.string_of_int i  in
            (uu____63142, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____63130  in
        FStar_All.pipe_right uu____63129
          (fun _63155  -> FStar_Extraction_ML_Syntax.MLE_Const _63155)
         in
      FStar_All.pipe_right uu____63128
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____63164 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _63165  -> FStar_Extraction_ML_Syntax.MLE_Const _63165)
         in
      FStar_All.pipe_right uu____63164
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____63166 =
      let uu____63173 =
        let uu____63176 =
          let uu____63177 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____63177 cstr  in
        let uu____63180 =
          let uu____63183 =
            let uu____63184 =
              let uu____63186 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____63186 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____63184 cint  in
          let uu____63189 =
            let uu____63192 =
              let uu____63193 =
                let uu____63195 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____63195 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____63193 cint  in
            let uu____63198 =
              let uu____63201 =
                let uu____63202 =
                  let uu____63204 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____63204 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____63202 cint  in
              let uu____63207 =
                let uu____63210 =
                  let uu____63211 =
                    let uu____63213 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____63213 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____63211 cint  in
                [uu____63210]  in
              uu____63201 :: uu____63207  in
            uu____63192 :: uu____63198  in
          uu____63183 :: uu____63189  in
        uu____63176 :: uu____63180  in
      (mk_range_mle, uu____63173)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____63166
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____63230 ->
          let uu____63231 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____63231
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____63259 =
            FStar_Util.find_opt
              (fun uu____63275  ->
                 match uu____63275 with | (y,uu____63283) -> y = x) subst1
             in
          (match uu____63259 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____63307 =
            let uu____63314 = subst_aux subst1 t1  in
            let uu____63315 = subst_aux subst1 t2  in
            (uu____63314, f, uu____63315)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____63307
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____63322 =
            let uu____63329 = FStar_List.map (subst_aux subst1) args  in
            (uu____63329, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____63322
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____63337 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____63337
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____63353  ->
    fun args  ->
      match uu____63353 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____63367 =
               let uu____63368 = FStar_List.zip formals args  in
               subst_aux uu____63368 t  in
             FStar_Pervasives_Native.Some uu____63367)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____63400 = try_subst ts args  in
      match uu____63400 with
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
    fun uu___617_63417  ->
      match uu___617_63417 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____63426 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____63426 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____63432 = try_subst ts args  in
               (match uu____63432 with
                | FStar_Pervasives_Native.None  ->
                    let uu____63437 =
                      let uu____63439 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____63441 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____63443 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____63439 uu____63441 uu____63443
                       in
                    failwith uu____63437
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____63450 -> FStar_Pervasives_Native.None)
      | uu____63453 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____63467) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____63471 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_63483  ->
    match uu___618_63483 with
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
        | uu____63504 ->
            let uu____63509 =
              let uu____63511 = FStar_Range.string_of_range r  in
              let uu____63513 = eff_to_string f  in
              let uu____63515 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____63511
                uu____63513 uu____63515
               in
            failwith uu____63509
  
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
    (fun uu____63558  ->
       fun t  ->
         match uu____63558 with
         | (uu____63565,t0) ->
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
                | uu____63688 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____63725 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____63733 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____63733 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____63744;
                     FStar_Extraction_ML_Syntax.loc = uu____63745;_}
                   ->
                   let uu____63770 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____63770
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____63788 = type_leq unfold_ty t2 t2'  in
                        (if uu____63788
                         then
                           let body1 =
                             let uu____63799 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____63799
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____63804 =
                             let uu____63807 =
                               let uu____63808 =
                                 let uu____63813 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____63813
                                  in
                               FStar_All.pipe_left uu____63808
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____63807  in
                           (true, uu____63804)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____63853 =
                           let uu____63861 =
                             let uu____63864 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _63867  ->
                                  FStar_Pervasives_Native.Some _63867)
                               uu____63864
                              in
                           type_leq_c unfold_ty uu____63861 t2 t2'  in
                         match uu____63853 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____63889 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____63889
                               | uu____63900 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____63912 ->
                   let uu____63915 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____63915
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____63955 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____63955
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____63977 = unfold_ty t  in
                 match uu____63977 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____63988 = unfold_ty t'  in
                     (match uu____63988 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____64009 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____64009
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____64033,uu____64034)
              ->
              let uu____64041 = unfold_ty t  in
              (match uu____64041 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____64052 -> (false, FStar_Pervasives_Native.None))
          | (uu____64059,FStar_Extraction_ML_Syntax.MLTY_Named uu____64060)
              ->
              let uu____64067 = unfold_ty t'  in
              (match uu____64067 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____64078 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____64089 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____64103 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____64103 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____64131 =
          let uu____64138 = erase_effect_annotations t1  in
          let uu____64139 = erase_effect_annotations t2  in
          (uu____64138, FStar_Extraction_ML_Syntax.E_PURE, uu____64139)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____64131
    | uu____64140 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_64168  ->
    match uu___619_64168 with
    | (FStar_Util.Inl uu____64180,uu____64181)::uu____64182 -> true
    | uu____64206 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____64234  ->
    match uu____64234 with
    | (ns,n1) ->
        let uu____64256 =
          let uu____64258 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____64258  in
        if uu____64256
        then
          let uu____64268 =
            let uu____64270 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____64270  in
          FStar_Pervasives_Native.Some uu____64268
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____64289 = is_xtuple mlp  in
        (match uu____64289 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____64296 -> e)
    | uu____64300 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_64311  ->
    match uu___620_64311 with
    | f::uu____64318 ->
        let uu____64321 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____64321 with
         | (ns,uu____64332) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____64345 -> failwith "impos"
  
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
  fun uu____64411  ->
    match uu____64411 with
    | (ns,n1) ->
        let uu____64433 =
          let uu____64435 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____64435  in
        if uu____64433
        then
          let uu____64445 =
            let uu____64447 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____64447  in
          FStar_Pervasives_Native.Some uu____64445
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____64466 = is_xtuple_ty mlp  in
        (match uu____64466 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____64473 -> t)
    | uu____64477 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____64491 = codegen_fsharp ()  in
    if uu____64491
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____64513  ->
    match uu____64513 with
    | (ns,n1) ->
        let uu____64533 = codegen_fsharp ()  in
        if uu____64533
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____64561 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____64561, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____64592 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____64592
      then true
      else
        (let uu____64599 = unfold_ty t  in
         match uu____64599 with
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
            let uu____64622 =
              let uu____64629 = eraseTypeDeep unfold_ty tyd  in
              let uu____64630 = eraseTypeDeep unfold_ty tycd  in
              (uu____64629, etag, uu____64630)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____64622
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____64639 = erasableType unfold_ty t  in
          if uu____64639
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____64644 =
               let uu____64651 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____64651, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____64644)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____64659 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____64659
      | uu____64662 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____64673 =
    let uu____64678 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____64678  in
  FStar_All.pipe_left uu____64673
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
          let uu____64766 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____64766
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____64782 = FStar_Range.file_of_range r  in (line, uu____64782)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64805,b) ->
        let uu____64807 = doms_and_cod b  in
        (match uu____64807 with | (ds,c) -> ((a :: ds), c))
    | uu____64828 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____64841 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____64841
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64869,b) ->
        let uu____64871 = uncurry_mlty_fun b  in
        (match uu____64871 with | (args,res) -> ((a :: args), res))
    | uu____64892 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____64908 -> true
    | uu____64911 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____64921 -> uu____64921
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____64943 =
          let uu____64949 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____64949)  in
        FStar_Errors.log_issue r uu____64943
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____64962 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____64973 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____64984 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____64995 -> false
  
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
              let uu____65066 =
                let uu____65067 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65067  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65066
               in
            let lid_to_top_name l =
              let uu____65074 =
                let uu____65075 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65075  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65074
               in
            let str_to_name s =
              let uu____65084 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____65084  in
            let str_to_top_name s =
              let uu____65093 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____65093  in
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
              let uu____65131 =
                let uu____65132 =
                  let uu____65139 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____65141 =
                    let uu____65144 =
                      let uu____65145 =
                        let uu____65146 =
                          let uu____65147 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____65147
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____65146  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____65145
                       in
                    [uu____65144]  in
                  (uu____65139, uu____65141)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65132  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65131
               in
            let emb_prefix uu___621_65162 =
              match uu___621_65162 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____65176 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____65187 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____65216 =
                let uu____65218 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____65218  in
              emb_prefix l uu____65216  in
            let mk_any_embedding l s =
              let uu____65234 =
                let uu____65235 =
                  let uu____65242 = emb_prefix l "mk_any_emb"  in
                  let uu____65244 =
                    let uu____65247 = str_to_name s  in [uu____65247]  in
                  (uu____65242, uu____65244)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65235  in
              FStar_All.pipe_left w uu____65234  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____65297 =
                let uu____65298 =
                  let uu____65305 = emb_prefix l "e_arrow"  in
                  (uu____65305, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65298  in
              FStar_All.pipe_left w uu____65297  in
            let known_type_constructors =
              let term_cs =
                let uu____65343 =
                  let uu____65358 =
                    let uu____65373 =
                      let uu____65388 =
                        let uu____65403 =
                          let uu____65418 =
                            let uu____65433 =
                              let uu____65448 =
                                let uu____65461 =
                                  let uu____65470 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____65470, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____65461, Syntax_term)  in
                              let uu____65484 =
                                let uu____65499 =
                                  let uu____65512 =
                                    let uu____65521 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____65521, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____65512, Refl_emb)  in
                                let uu____65535 =
                                  let uu____65550 =
                                    let uu____65563 =
                                      let uu____65572 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____65572, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____65563, Refl_emb)  in
                                  let uu____65586 =
                                    let uu____65601 =
                                      let uu____65614 =
                                        let uu____65623 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____65623, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____65614, Refl_emb)  in
                                    let uu____65637 =
                                      let uu____65652 =
                                        let uu____65665 =
                                          let uu____65674 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____65674,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____65665, Refl_emb)  in
                                      let uu____65688 =
                                        let uu____65703 =
                                          let uu____65716 =
                                            let uu____65725 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____65725,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____65716, Refl_emb)  in
                                        [uu____65703]  in
                                      uu____65652 :: uu____65688  in
                                    uu____65601 :: uu____65637  in
                                  uu____65550 :: uu____65586  in
                                uu____65499 :: uu____65535  in
                              uu____65448 :: uu____65484  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____65433
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____65418
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____65403
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____65388
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____65373
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____65358
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____65343
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_66032  ->
                     match uu___622_66032 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____66107 -> failwith "Impossible") term_cs
                 in
              fun uu___623_66133  ->
                match uu___623_66133 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____66148 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____66185  ->
                   match uu____66185 with
                   | ((x,args,uu____66201),uu____66202) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____66232 =
              match uu____66232 with
              | (bv',uu____66240) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____66274 =
                let uu____66275 = FStar_Syntax_Subst.compress t3  in
                uu____66275.FStar_Syntax_Syntax.n  in
              match uu____66274 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____66284 =
                    let uu____66286 =
                      let uu____66292 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____66292  in
                    FStar_Pervasives_Native.snd uu____66286  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____66284
              | FStar_Syntax_Syntax.Tm_refine (x,uu____66313) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____66319,uu____66320)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____66393 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____66393 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____66415 =
                           let uu____66416 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____66416  in
                         uu____66415.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____66434 = mk_embedding l env t0  in
                       let uu____66435 = mk_embedding l env t11  in
                       emb_arrow l uu____66434 uu____66435)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____66506 =
                      let uu____66513 =
                        let uu____66514 =
                          let uu____66529 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____66529)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____66514  in
                      FStar_Syntax_Syntax.mk uu____66513  in
                    uu____66506 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____66554 ->
                  let uu____66555 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66555 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66607 =
                         let uu____66608 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66608.FStar_Syntax_Syntax.n  in
                       (match uu____66607 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66634  ->
                                      match uu____66634 with
                                      | (t4,uu____66642) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66649 =
                              let uu____66662 =
                                FStar_Util.find_opt
                                  (fun uu____66694  ->
                                     match uu____66694 with
                                     | ((x,uu____66709,uu____66710),uu____66711)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66662
                                FStar_Util.must
                               in
                            (match uu____66649 with
                             | ((uu____66762,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _66779 when
                                      _66779 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____66784 ->
                            let uu____66785 =
                              let uu____66786 =
                                let uu____66788 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____66788
                                 in
                              NoTacticEmbedding uu____66786  in
                            FStar_Exn.raise uu____66785))
              | FStar_Syntax_Syntax.Tm_uinst uu____66791 ->
                  let uu____66798 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66798 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66850 =
                         let uu____66851 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66851.FStar_Syntax_Syntax.n  in
                       (match uu____66850 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66877  ->
                                      match uu____66877 with
                                      | (t4,uu____66885) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66892 =
                              let uu____66905 =
                                FStar_Util.find_opt
                                  (fun uu____66937  ->
                                     match uu____66937 with
                                     | ((x,uu____66952,uu____66953),uu____66954)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66905
                                FStar_Util.must
                               in
                            (match uu____66892 with
                             | ((uu____67005,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67022 when
                                      _67022 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67027 ->
                            let uu____67028 =
                              let uu____67029 =
                                let uu____67031 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67031
                                 in
                              NoTacticEmbedding uu____67029  in
                            FStar_Exn.raise uu____67028))
              | FStar_Syntax_Syntax.Tm_app uu____67034 ->
                  let uu____67051 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____67051 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____67103 =
                         let uu____67104 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____67104.FStar_Syntax_Syntax.n  in
                       (match uu____67103 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____67130  ->
                                      match uu____67130 with
                                      | (t4,uu____67138) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____67145 =
                              let uu____67158 =
                                FStar_Util.find_opt
                                  (fun uu____67190  ->
                                     match uu____67190 with
                                     | ((x,uu____67205,uu____67206),uu____67207)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____67158
                                FStar_Util.must
                               in
                            (match uu____67145 with
                             | ((uu____67258,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67275 when
                                      _67275 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67280 ->
                            let uu____67281 =
                              let uu____67282 =
                                let uu____67284 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67284
                                 in
                              NoTacticEmbedding uu____67282  in
                            FStar_Exn.raise uu____67281))
              | uu____67287 ->
                  let uu____67288 =
                    let uu____67289 =
                      let uu____67291 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____67291
                       in
                    NoTacticEmbedding uu____67289  in
                  FStar_Exn.raise uu____67288
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____67313 =
                      let uu____67314 =
                        let uu____67321 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67323 =
                          let uu____67326 =
                            let uu____67327 =
                              let uu____67328 =
                                let uu____67329 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67329
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67328
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67327
                             in
                          let uu____67331 =
                            let uu____67334 =
                              let uu____67335 =
                                let uu____67336 =
                                  let uu____67337 =
                                    let uu____67344 =
                                      let uu____67347 = str_to_name "args"
                                         in
                                      [uu____67347]  in
                                    (body, uu____67344)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____67337
                                   in
                                FStar_All.pipe_left w uu____67336  in
                              mk_lam "_" uu____67335  in
                            [uu____67334]  in
                          uu____67326 :: uu____67331  in
                        (uu____67321, uu____67323)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67314  in
                    FStar_All.pipe_left w uu____67313  in
                  mk_lam "args" body1
              | uu____67355 ->
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
                    let uu____67404 =
                      let uu____67405 =
                        let uu____67406 =
                          let uu____67413 =
                            let uu____67416 = str_to_name "args"  in
                            [uu____67416]  in
                          (body, uu____67413)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67406  in
                      FStar_All.pipe_left w uu____67405  in
                    (pattern, FStar_Pervasives_Native.None, uu____67404)  in
                  let default_branch =
                    let uu____67431 =
                      let uu____67432 =
                        let uu____67433 =
                          let uu____67440 = str_to_name "failwith"  in
                          let uu____67442 =
                            let uu____67445 =
                              let uu____67446 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____67446  in
                            [uu____67445]  in
                          (uu____67440, uu____67442)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67433  in
                      FStar_All.pipe_left w uu____67432  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____67431)
                     in
                  let body1 =
                    let uu____67454 =
                      let uu____67455 =
                        let uu____67470 = str_to_name "args"  in
                        (uu____67470, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____67455  in
                    FStar_All.pipe_left w uu____67454  in
                  let body2 =
                    let uu____67507 =
                      let uu____67508 =
                        let uu____67515 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67517 =
                          let uu____67520 =
                            let uu____67521 =
                              let uu____67522 =
                                let uu____67523 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67523
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67522
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67521
                             in
                          let uu____67525 =
                            let uu____67528 = mk_lam "_" body1  in
                            [uu____67528]  in
                          uu____67520 :: uu____67525  in
                        (uu____67515, uu____67517)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67508  in
                    FStar_All.pipe_left w uu____67507  in
                  mk_lam "args" body2
               in
            let uu____67533 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____67533 with
            | (bs,c) ->
                let uu____67566 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____67659 = FStar_Util.first_N n1 bs  in
                           match uu____67659 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____67737 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____67737
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____67754 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____67756 = FStar_Util.string_of_int n1
                                in
                             let uu____67758 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____67754 uu____67756 uu____67758
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____67566 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____67809 =
                       let uu____67830 =
                         FStar_Util.prefix_until
                           (fun uu____67872  ->
                              match uu____67872 with
                              | (b,uu____67881) ->
                                  let uu____67886 =
                                    let uu____67887 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____67887.FStar_Syntax_Syntax.n  in
                                  (match uu____67886 with
                                   | FStar_Syntax_Syntax.Tm_type uu____67891
                                       -> false
                                   | uu____67893 -> true)) bs1
                          in
                       match uu____67830 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____67809 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____68135 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____68135) type_vars
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
                                let uu____68235 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____68235
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____68252 =
                                      let uu____68255 =
                                        let uu____68258 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____68259 =
                                          let uu____68262 =
                                            let uu____68263 =
                                              let uu____68264 =
                                                let uu____68265 =
                                                  let uu____68277 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____68277,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____68265
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____68264
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____68263
                                             in
                                          [uu____68262; fv_lid_embedded; cb]
                                           in
                                        uu____68258 :: uu____68259  in
                                      res_embedding :: uu____68255  in
                                    FStar_List.append arg_unembeddings
                                      uu____68252
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
                                  let uu____68296 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____68296, arity, true)
                                else
                                  (let uu____68306 =
                                     let uu____68308 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____68308
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____68306
                                   then
                                     let h =
                                       let uu____68319 =
                                         let uu____68321 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____68321
                                          in
                                       str_to_top_name uu____68319  in
                                     let tac_fun =
                                       let uu____68324 =
                                         let uu____68325 =
                                           let uu____68332 =
                                             let uu____68333 =
                                               let uu____68335 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____68335
                                                in
                                             str_to_top_name uu____68333  in
                                           let uu____68337 =
                                             let uu____68340 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____68340]  in
                                           (uu____68332, uu____68337)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____68325
                                          in
                                       FStar_All.pipe_left w uu____68324  in
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
                                           let uu____68354 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____68354
                                       | uu____68358 ->
                                           let uu____68362 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____68362
                                        in
                                     let uu____68365 =
                                       let uu____68366 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____68366  in
                                     (uu____68365,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____68375 =
                                        let uu____68376 =
                                          let uu____68378 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____68378
                                           in
                                        NoTacticEmbedding uu____68376  in
                                      FStar_Exn.raise uu____68375))
                            | (b,uu____68390)::bs4 ->
                                let uu____68410 =
                                  let uu____68413 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____68413 :: accum_embeddings  in
                                aux loc uu____68410 bs4
                             in
                          (try
                             (fun uu___1304_68435  ->
                                match () with
                                | () ->
                                    let uu____68448 = aux Syntax_term [] bs2
                                       in
                                    (match uu____68448 with
                                     | (w1,a,b) ->
                                         let uu____68476 = aux NBE_t [] bs2
                                            in
                                         (match uu____68476 with
                                          | (w',uu____68498,uu____68499) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____68535 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____68535 msg);
                                FStar_Pervasives_Native.None))))
  