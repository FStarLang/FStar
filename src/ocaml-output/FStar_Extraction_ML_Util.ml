open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____62940  ->
    let uu____62941 = FStar_Options.codegen ()  in
    uu____62941 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____63010 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____63040) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____63046) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____63051 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____63055 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_63069  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_63072 ->
          let uu____63073 =
            let uu____63075 = FStar_Range.string_of_range p  in
            let uu____63077 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____63075 uu____63077
             in
          failwith uu____63073
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____63094 =
        let uu____63095 =
          let uu____63096 =
            let uu____63108 = FStar_Util.string_of_int i  in
            (uu____63108, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____63096  in
        FStar_All.pipe_right uu____63095
          (fun _63121  -> FStar_Extraction_ML_Syntax.MLE_Const _63121)
         in
      FStar_All.pipe_right uu____63094
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____63130 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _63131  -> FStar_Extraction_ML_Syntax.MLE_Const _63131)
         in
      FStar_All.pipe_right uu____63130
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____63132 =
      let uu____63139 =
        let uu____63142 =
          let uu____63143 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____63143 cstr  in
        let uu____63146 =
          let uu____63149 =
            let uu____63150 =
              let uu____63152 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____63152 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____63150 cint  in
          let uu____63155 =
            let uu____63158 =
              let uu____63159 =
                let uu____63161 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____63161 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____63159 cint  in
            let uu____63164 =
              let uu____63167 =
                let uu____63168 =
                  let uu____63170 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____63170 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____63168 cint  in
              let uu____63173 =
                let uu____63176 =
                  let uu____63177 =
                    let uu____63179 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____63179 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____63177 cint  in
                [uu____63176]  in
              uu____63167 :: uu____63173  in
            uu____63158 :: uu____63164  in
          uu____63149 :: uu____63155  in
        uu____63142 :: uu____63146  in
      (mk_range_mle, uu____63139)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____63132
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____63196 ->
          let uu____63197 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____63197
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____63225 =
            FStar_Util.find_opt
              (fun uu____63241  ->
                 match uu____63241 with | (y,uu____63249) -> y = x) subst1
             in
          (match uu____63225 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____63273 =
            let uu____63280 = subst_aux subst1 t1  in
            let uu____63281 = subst_aux subst1 t2  in
            (uu____63280, f, uu____63281)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____63273
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____63288 =
            let uu____63295 = FStar_List.map (subst_aux subst1) args  in
            (uu____63295, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____63288
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____63303 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____63303
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____63319  ->
    fun args  ->
      match uu____63319 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____63333 =
               let uu____63334 = FStar_List.zip formals args  in
               subst_aux uu____63334 t  in
             FStar_Pervasives_Native.Some uu____63333)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____63366 = try_subst ts args  in
      match uu____63366 with
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
    fun uu___617_63383  ->
      match uu___617_63383 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____63392 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____63392 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____63398 = try_subst ts args  in
               (match uu____63398 with
                | FStar_Pervasives_Native.None  ->
                    let uu____63403 =
                      let uu____63405 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____63407 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____63409 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____63405 uu____63407 uu____63409
                       in
                    failwith uu____63403
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____63416 -> FStar_Pervasives_Native.None)
      | uu____63419 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____63433) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____63437 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_63449  ->
    match uu___618_63449 with
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
        | uu____63470 ->
            let uu____63475 =
              let uu____63477 = FStar_Range.string_of_range r  in
              let uu____63479 = eff_to_string f  in
              let uu____63481 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____63477
                uu____63479 uu____63481
               in
            failwith uu____63475
  
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
    (fun uu____63524  ->
       fun t  ->
         match uu____63524 with
         | (uu____63531,t0) ->
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
                | uu____63654 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____63691 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____63699 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____63699 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____63710;
                     FStar_Extraction_ML_Syntax.loc = uu____63711;_}
                   ->
                   let uu____63736 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____63736
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____63754 = type_leq unfold_ty t2 t2'  in
                        (if uu____63754
                         then
                           let body1 =
                             let uu____63765 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____63765
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____63770 =
                             let uu____63773 =
                               let uu____63774 =
                                 let uu____63779 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____63779
                                  in
                               FStar_All.pipe_left uu____63774
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____63773  in
                           (true, uu____63770)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____63819 =
                           let uu____63827 =
                             let uu____63830 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _63833  ->
                                  FStar_Pervasives_Native.Some _63833)
                               uu____63830
                              in
                           type_leq_c unfold_ty uu____63827 t2 t2'  in
                         match uu____63819 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____63855 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____63855
                               | uu____63866 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____63878 ->
                   let uu____63881 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____63881
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____63921 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____63921
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____63943 = unfold_ty t  in
                 match uu____63943 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____63954 = unfold_ty t'  in
                     (match uu____63954 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____63975 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____63975
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____63999,uu____64000)
              ->
              let uu____64007 = unfold_ty t  in
              (match uu____64007 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____64018 -> (false, FStar_Pervasives_Native.None))
          | (uu____64025,FStar_Extraction_ML_Syntax.MLTY_Named uu____64026)
              ->
              let uu____64033 = unfold_ty t'  in
              (match uu____64033 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____64044 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____64055 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____64069 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____64069 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____64097 =
          let uu____64104 = erase_effect_annotations t1  in
          let uu____64105 = erase_effect_annotations t2  in
          (uu____64104, FStar_Extraction_ML_Syntax.E_PURE, uu____64105)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____64097
    | uu____64106 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_64134  ->
    match uu___619_64134 with
    | (FStar_Util.Inl uu____64146,uu____64147)::uu____64148 -> true
    | uu____64172 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____64200  ->
    match uu____64200 with
    | (ns,n1) ->
        let uu____64222 =
          let uu____64224 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____64224  in
        if uu____64222
        then
          let uu____64234 =
            let uu____64236 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____64236  in
          FStar_Pervasives_Native.Some uu____64234
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____64255 = is_xtuple mlp  in
        (match uu____64255 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____64262 -> e)
    | uu____64266 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_64277  ->
    match uu___620_64277 with
    | f::uu____64284 ->
        let uu____64287 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____64287 with
         | (ns,uu____64298) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____64311 -> failwith "impos"
  
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
  fun uu____64377  ->
    match uu____64377 with
    | (ns,n1) ->
        let uu____64399 =
          let uu____64401 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____64401  in
        if uu____64399
        then
          let uu____64411 =
            let uu____64413 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____64413  in
          FStar_Pervasives_Native.Some uu____64411
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____64432 = is_xtuple_ty mlp  in
        (match uu____64432 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____64439 -> t)
    | uu____64443 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____64457 = codegen_fsharp ()  in
    if uu____64457
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____64479  ->
    match uu____64479 with
    | (ns,n1) ->
        let uu____64499 = codegen_fsharp ()  in
        if uu____64499
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____64527 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____64527, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____64558 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____64558
      then true
      else
        (let uu____64565 = unfold_ty t  in
         match uu____64565 with
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
            let uu____64588 =
              let uu____64595 = eraseTypeDeep unfold_ty tyd  in
              let uu____64596 = eraseTypeDeep unfold_ty tycd  in
              (uu____64595, etag, uu____64596)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____64588
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____64605 = erasableType unfold_ty t  in
          if uu____64605
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____64610 =
               let uu____64617 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____64617, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____64610)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____64625 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____64625
      | uu____64628 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____64639 =
    let uu____64644 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____64644  in
  FStar_All.pipe_left uu____64639
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
          let uu____64732 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____64732
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____64748 = FStar_Range.file_of_range r  in (line, uu____64748)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64771,b) ->
        let uu____64773 = doms_and_cod b  in
        (match uu____64773 with | (ds,c) -> ((a :: ds), c))
    | uu____64794 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____64807 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____64807
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64835,b) ->
        let uu____64837 = uncurry_mlty_fun b  in
        (match uu____64837 with | (args,res) -> ((a :: args), res))
    | uu____64858 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____64874 -> true
    | uu____64877 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____64887 -> uu____64887
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____64909 =
          let uu____64915 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____64915)  in
        FStar_Errors.log_issue r uu____64909
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____64928 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____64939 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____64950 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____64961 -> false
  
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
              let uu____65032 =
                let uu____65033 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65033  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65032
               in
            let lid_to_top_name l =
              let uu____65040 =
                let uu____65041 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65041  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65040
               in
            let str_to_name s =
              let uu____65050 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____65050  in
            let str_to_top_name s =
              let uu____65059 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____65059  in
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
              let uu____65097 =
                let uu____65098 =
                  let uu____65105 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____65107 =
                    let uu____65110 =
                      let uu____65111 =
                        let uu____65112 =
                          let uu____65113 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____65113
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____65112  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____65111
                       in
                    [uu____65110]  in
                  (uu____65105, uu____65107)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65098  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65097
               in
            let emb_prefix uu___621_65128 =
              match uu___621_65128 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____65142 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____65153 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____65182 =
                let uu____65184 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____65184  in
              emb_prefix l uu____65182  in
            let mk_any_embedding l s =
              let uu____65200 =
                let uu____65201 =
                  let uu____65208 = emb_prefix l "mk_any_emb"  in
                  let uu____65210 =
                    let uu____65213 = str_to_name s  in [uu____65213]  in
                  (uu____65208, uu____65210)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65201  in
              FStar_All.pipe_left w uu____65200  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____65263 =
                let uu____65264 =
                  let uu____65271 = emb_prefix l "e_arrow"  in
                  (uu____65271, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65264  in
              FStar_All.pipe_left w uu____65263  in
            let known_type_constructors =
              let term_cs =
                let uu____65309 =
                  let uu____65324 =
                    let uu____65339 =
                      let uu____65354 =
                        let uu____65369 =
                          let uu____65384 =
                            let uu____65399 =
                              let uu____65414 =
                                let uu____65427 =
                                  let uu____65436 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____65436, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____65427, Syntax_term)  in
                              let uu____65450 =
                                let uu____65465 =
                                  let uu____65478 =
                                    let uu____65487 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____65487, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____65478, Refl_emb)  in
                                let uu____65501 =
                                  let uu____65516 =
                                    let uu____65529 =
                                      let uu____65538 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____65538, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____65529, Refl_emb)  in
                                  let uu____65552 =
                                    let uu____65567 =
                                      let uu____65580 =
                                        let uu____65589 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____65589, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____65580, Refl_emb)  in
                                    let uu____65603 =
                                      let uu____65618 =
                                        let uu____65631 =
                                          let uu____65640 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____65640,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____65631, Refl_emb)  in
                                      let uu____65654 =
                                        let uu____65669 =
                                          let uu____65682 =
                                            let uu____65691 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____65691,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____65682, Refl_emb)  in
                                        [uu____65669]  in
                                      uu____65618 :: uu____65654  in
                                    uu____65567 :: uu____65603  in
                                  uu____65516 :: uu____65552  in
                                uu____65465 :: uu____65501  in
                              uu____65414 :: uu____65450  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____65399
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____65384
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____65369
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____65354
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____65339
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____65324
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____65309
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_65998  ->
                     match uu___622_65998 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____66073 -> failwith "Impossible") term_cs
                 in
              fun uu___623_66099  ->
                match uu___623_66099 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____66114 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____66151  ->
                   match uu____66151 with
                   | ((x,args,uu____66167),uu____66168) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____66198 =
              match uu____66198 with
              | (bv',uu____66206) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____66240 =
                let uu____66241 = FStar_Syntax_Subst.compress t3  in
                uu____66241.FStar_Syntax_Syntax.n  in
              match uu____66240 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____66250 =
                    let uu____66252 =
                      let uu____66258 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____66258  in
                    FStar_Pervasives_Native.snd uu____66252  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____66250
              | FStar_Syntax_Syntax.Tm_refine (x,uu____66279) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____66285,uu____66286)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____66359 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____66359 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____66381 =
                           let uu____66382 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____66382  in
                         uu____66381.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____66400 = mk_embedding l env t0  in
                       let uu____66401 = mk_embedding l env t11  in
                       emb_arrow l uu____66400 uu____66401)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____66472 =
                      let uu____66479 =
                        let uu____66480 =
                          let uu____66495 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____66495)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____66480  in
                      FStar_Syntax_Syntax.mk uu____66479  in
                    uu____66472 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____66520 ->
                  let uu____66521 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66521 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66573 =
                         let uu____66574 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66574.FStar_Syntax_Syntax.n  in
                       (match uu____66573 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66600  ->
                                      match uu____66600 with
                                      | (t4,uu____66608) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66615 =
                              let uu____66628 =
                                FStar_Util.find_opt
                                  (fun uu____66660  ->
                                     match uu____66660 with
                                     | ((x,uu____66675,uu____66676),uu____66677)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66628
                                FStar_Util.must
                               in
                            (match uu____66615 with
                             | ((uu____66728,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _66745 when
                                      _66745 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____66750 ->
                            let uu____66751 =
                              let uu____66752 =
                                let uu____66754 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____66754
                                 in
                              NoTacticEmbedding uu____66752  in
                            FStar_Exn.raise uu____66751))
              | FStar_Syntax_Syntax.Tm_uinst uu____66757 ->
                  let uu____66764 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66764 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66816 =
                         let uu____66817 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66817.FStar_Syntax_Syntax.n  in
                       (match uu____66816 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66843  ->
                                      match uu____66843 with
                                      | (t4,uu____66851) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66858 =
                              let uu____66871 =
                                FStar_Util.find_opt
                                  (fun uu____66903  ->
                                     match uu____66903 with
                                     | ((x,uu____66918,uu____66919),uu____66920)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66871
                                FStar_Util.must
                               in
                            (match uu____66858 with
                             | ((uu____66971,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _66988 when
                                      _66988 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____66993 ->
                            let uu____66994 =
                              let uu____66995 =
                                let uu____66997 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____66997
                                 in
                              NoTacticEmbedding uu____66995  in
                            FStar_Exn.raise uu____66994))
              | FStar_Syntax_Syntax.Tm_app uu____67000 ->
                  let uu____67017 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____67017 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____67069 =
                         let uu____67070 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____67070.FStar_Syntax_Syntax.n  in
                       (match uu____67069 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____67096  ->
                                      match uu____67096 with
                                      | (t4,uu____67104) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____67111 =
                              let uu____67124 =
                                FStar_Util.find_opt
                                  (fun uu____67156  ->
                                     match uu____67156 with
                                     | ((x,uu____67171,uu____67172),uu____67173)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____67124
                                FStar_Util.must
                               in
                            (match uu____67111 with
                             | ((uu____67224,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67241 when
                                      _67241 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67246 ->
                            let uu____67247 =
                              let uu____67248 =
                                let uu____67250 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67250
                                 in
                              NoTacticEmbedding uu____67248  in
                            FStar_Exn.raise uu____67247))
              | uu____67253 ->
                  let uu____67254 =
                    let uu____67255 =
                      let uu____67257 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____67257
                       in
                    NoTacticEmbedding uu____67255  in
                  FStar_Exn.raise uu____67254
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____67279 =
                      let uu____67280 =
                        let uu____67287 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67289 =
                          let uu____67292 =
                            let uu____67293 =
                              let uu____67294 =
                                let uu____67295 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67295
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67294
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67293
                             in
                          let uu____67297 =
                            let uu____67300 =
                              let uu____67301 =
                                let uu____67302 =
                                  let uu____67303 =
                                    let uu____67310 =
                                      let uu____67313 = str_to_name "args"
                                         in
                                      [uu____67313]  in
                                    (body, uu____67310)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____67303
                                   in
                                FStar_All.pipe_left w uu____67302  in
                              mk_lam "_" uu____67301  in
                            [uu____67300]  in
                          uu____67292 :: uu____67297  in
                        (uu____67287, uu____67289)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67280  in
                    FStar_All.pipe_left w uu____67279  in
                  mk_lam "args" body1
              | uu____67321 ->
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
                    let uu____67370 =
                      let uu____67371 =
                        let uu____67372 =
                          let uu____67379 =
                            let uu____67382 = str_to_name "args"  in
                            [uu____67382]  in
                          (body, uu____67379)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67372  in
                      FStar_All.pipe_left w uu____67371  in
                    (pattern, FStar_Pervasives_Native.None, uu____67370)  in
                  let default_branch =
                    let uu____67397 =
                      let uu____67398 =
                        let uu____67399 =
                          let uu____67406 = str_to_name "failwith"  in
                          let uu____67408 =
                            let uu____67411 =
                              let uu____67412 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____67412  in
                            [uu____67411]  in
                          (uu____67406, uu____67408)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67399  in
                      FStar_All.pipe_left w uu____67398  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____67397)
                     in
                  let body1 =
                    let uu____67420 =
                      let uu____67421 =
                        let uu____67436 = str_to_name "args"  in
                        (uu____67436, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____67421  in
                    FStar_All.pipe_left w uu____67420  in
                  let body2 =
                    let uu____67473 =
                      let uu____67474 =
                        let uu____67481 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67483 =
                          let uu____67486 =
                            let uu____67487 =
                              let uu____67488 =
                                let uu____67489 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67489
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67488
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67487
                             in
                          let uu____67491 =
                            let uu____67494 = mk_lam "_" body1  in
                            [uu____67494]  in
                          uu____67486 :: uu____67491  in
                        (uu____67481, uu____67483)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67474  in
                    FStar_All.pipe_left w uu____67473  in
                  mk_lam "args" body2
               in
            let uu____67499 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____67499 with
            | (bs,c) ->
                let uu____67532 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____67625 = FStar_Util.first_N n1 bs  in
                           match uu____67625 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____67703 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____67703
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____67720 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____67722 = FStar_Util.string_of_int n1
                                in
                             let uu____67724 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____67720 uu____67722 uu____67724
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____67532 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____67775 =
                       let uu____67796 =
                         FStar_Util.prefix_until
                           (fun uu____67838  ->
                              match uu____67838 with
                              | (b,uu____67847) ->
                                  let uu____67852 =
                                    let uu____67853 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____67853.FStar_Syntax_Syntax.n  in
                                  (match uu____67852 with
                                   | FStar_Syntax_Syntax.Tm_type uu____67857
                                       -> false
                                   | uu____67859 -> true)) bs1
                          in
                       match uu____67796 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____67775 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____68101 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____68101) type_vars
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
                                let uu____68201 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____68201
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____68218 =
                                      let uu____68221 =
                                        let uu____68224 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____68225 =
                                          let uu____68228 =
                                            let uu____68229 =
                                              let uu____68230 =
                                                let uu____68231 =
                                                  let uu____68243 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____68243,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____68231
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____68230
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____68229
                                             in
                                          [uu____68228; fv_lid_embedded; cb]
                                           in
                                        uu____68224 :: uu____68225  in
                                      res_embedding :: uu____68221  in
                                    FStar_List.append arg_unembeddings
                                      uu____68218
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
                                  let uu____68262 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____68262, arity, true)
                                else
                                  (let uu____68272 =
                                     let uu____68274 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____68274
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____68272
                                   then
                                     let h =
                                       let uu____68285 =
                                         let uu____68287 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____68287
                                          in
                                       str_to_top_name uu____68285  in
                                     let tac_fun =
                                       let uu____68290 =
                                         let uu____68291 =
                                           let uu____68298 =
                                             let uu____68299 =
                                               let uu____68301 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____68301
                                                in
                                             str_to_top_name uu____68299  in
                                           let uu____68303 =
                                             let uu____68306 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____68306]  in
                                           (uu____68298, uu____68303)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____68291
                                          in
                                       FStar_All.pipe_left w uu____68290  in
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
                                           let uu____68320 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____68320
                                       | uu____68324 ->
                                           let uu____68328 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____68328
                                        in
                                     let uu____68331 =
                                       let uu____68332 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____68332  in
                                     (uu____68331,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____68341 =
                                        let uu____68342 =
                                          let uu____68344 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____68344
                                           in
                                        NoTacticEmbedding uu____68342  in
                                      FStar_Exn.raise uu____68341))
                            | (b,uu____68356)::bs4 ->
                                let uu____68376 =
                                  let uu____68379 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____68379 :: accum_embeddings  in
                                aux loc uu____68376 bs4
                             in
                          (try
                             (fun uu___1304_68401  ->
                                match () with
                                | () ->
                                    let uu____68414 = aux Syntax_term [] bs2
                                       in
                                    (match uu____68414 with
                                     | (w1,a,b) ->
                                         let uu____68442 = aux NBE_t [] bs2
                                            in
                                         (match uu____68442 with
                                          | (w',uu____68464,uu____68465) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____68501 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____68501 msg);
                                FStar_Pervasives_Native.None))))
  