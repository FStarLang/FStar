open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____62941  ->
    let uu____62942 = FStar_Options.codegen ()  in
    uu____62942 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____63011 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____63041) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____63047) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____63052 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____63056 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_63070  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_63073 ->
          let uu____63074 =
            let uu____63076 = FStar_Range.string_of_range p  in
            let uu____63078 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____63076 uu____63078
             in
          failwith uu____63074
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____63095 =
        let uu____63096 =
          let uu____63097 =
            let uu____63109 = FStar_Util.string_of_int i  in
            (uu____63109, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____63097  in
        FStar_All.pipe_right uu____63096
          (fun _63122  -> FStar_Extraction_ML_Syntax.MLE_Const _63122)
         in
      FStar_All.pipe_right uu____63095
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____63131 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _63132  -> FStar_Extraction_ML_Syntax.MLE_Const _63132)
         in
      FStar_All.pipe_right uu____63131
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____63133 =
      let uu____63140 =
        let uu____63143 =
          let uu____63144 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____63144 cstr  in
        let uu____63147 =
          let uu____63150 =
            let uu____63151 =
              let uu____63153 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____63153 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____63151 cint  in
          let uu____63156 =
            let uu____63159 =
              let uu____63160 =
                let uu____63162 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____63162 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____63160 cint  in
            let uu____63165 =
              let uu____63168 =
                let uu____63169 =
                  let uu____63171 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____63171 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____63169 cint  in
              let uu____63174 =
                let uu____63177 =
                  let uu____63178 =
                    let uu____63180 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____63180 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____63178 cint  in
                [uu____63177]  in
              uu____63168 :: uu____63174  in
            uu____63159 :: uu____63165  in
          uu____63150 :: uu____63156  in
        uu____63143 :: uu____63147  in
      (mk_range_mle, uu____63140)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____63133
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____63197 ->
          let uu____63198 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____63198
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____63226 =
            FStar_Util.find_opt
              (fun uu____63242  ->
                 match uu____63242 with | (y,uu____63250) -> y = x) subst1
             in
          (match uu____63226 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____63274 =
            let uu____63281 = subst_aux subst1 t1  in
            let uu____63282 = subst_aux subst1 t2  in
            (uu____63281, f, uu____63282)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____63274
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____63289 =
            let uu____63296 = FStar_List.map (subst_aux subst1) args  in
            (uu____63296, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____63289
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____63304 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____63304
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____63320  ->
    fun args  ->
      match uu____63320 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____63334 =
               let uu____63335 = FStar_List.zip formals args  in
               subst_aux uu____63335 t  in
             FStar_Pervasives_Native.Some uu____63334)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____63367 = try_subst ts args  in
      match uu____63367 with
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
    fun uu___617_63384  ->
      match uu___617_63384 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____63393 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____63393 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____63399 = try_subst ts args  in
               (match uu____63399 with
                | FStar_Pervasives_Native.None  ->
                    let uu____63404 =
                      let uu____63406 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____63408 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____63410 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____63406 uu____63408 uu____63410
                       in
                    failwith uu____63404
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____63417 -> FStar_Pervasives_Native.None)
      | uu____63420 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____63434) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____63438 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_63450  ->
    match uu___618_63450 with
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
        | uu____63471 ->
            let uu____63476 =
              let uu____63478 = FStar_Range.string_of_range r  in
              let uu____63480 = eff_to_string f  in
              let uu____63482 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____63478
                uu____63480 uu____63482
               in
            failwith uu____63476
  
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
    (fun uu____63525  ->
       fun t  ->
         match uu____63525 with
         | (uu____63532,t0) ->
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
                | uu____63655 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____63692 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____63700 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____63700 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____63711;
                     FStar_Extraction_ML_Syntax.loc = uu____63712;_}
                   ->
                   let uu____63737 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____63737
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____63755 = type_leq unfold_ty t2 t2'  in
                        (if uu____63755
                         then
                           let body1 =
                             let uu____63766 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____63766
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____63771 =
                             let uu____63774 =
                               let uu____63775 =
                                 let uu____63780 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____63780
                                  in
                               FStar_All.pipe_left uu____63775
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____63774  in
                           (true, uu____63771)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____63820 =
                           let uu____63828 =
                             let uu____63831 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _63834  ->
                                  FStar_Pervasives_Native.Some _63834)
                               uu____63831
                              in
                           type_leq_c unfold_ty uu____63828 t2 t2'  in
                         match uu____63820 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____63856 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____63856
                               | uu____63867 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____63879 ->
                   let uu____63882 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____63882
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____63922 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____63922
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____63944 = unfold_ty t  in
                 match uu____63944 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____63955 = unfold_ty t'  in
                     (match uu____63955 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____63976 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____63976
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____64000,uu____64001)
              ->
              let uu____64008 = unfold_ty t  in
              (match uu____64008 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____64019 -> (false, FStar_Pervasives_Native.None))
          | (uu____64026,FStar_Extraction_ML_Syntax.MLTY_Named uu____64027)
              ->
              let uu____64034 = unfold_ty t'  in
              (match uu____64034 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____64045 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____64056 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____64070 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____64070 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____64098 =
          let uu____64105 = erase_effect_annotations t1  in
          let uu____64106 = erase_effect_annotations t2  in
          (uu____64105, FStar_Extraction_ML_Syntax.E_PURE, uu____64106)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____64098
    | uu____64107 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_64135  ->
    match uu___619_64135 with
    | (FStar_Util.Inl uu____64147,uu____64148)::uu____64149 -> true
    | uu____64173 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____64201  ->
    match uu____64201 with
    | (ns,n1) ->
        let uu____64223 =
          let uu____64225 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____64225  in
        if uu____64223
        then
          let uu____64235 =
            let uu____64237 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____64237  in
          FStar_Pervasives_Native.Some uu____64235
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____64256 = is_xtuple mlp  in
        (match uu____64256 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____64263 -> e)
    | uu____64267 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_64278  ->
    match uu___620_64278 with
    | f::uu____64285 ->
        let uu____64288 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____64288 with
         | (ns,uu____64299) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____64312 -> failwith "impos"
  
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
  fun uu____64378  ->
    match uu____64378 with
    | (ns,n1) ->
        let uu____64400 =
          let uu____64402 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____64402  in
        if uu____64400
        then
          let uu____64412 =
            let uu____64414 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____64414  in
          FStar_Pervasives_Native.Some uu____64412
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____64433 = is_xtuple_ty mlp  in
        (match uu____64433 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____64440 -> t)
    | uu____64444 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____64458 = codegen_fsharp ()  in
    if uu____64458
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____64480  ->
    match uu____64480 with
    | (ns,n1) ->
        let uu____64500 = codegen_fsharp ()  in
        if uu____64500
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____64528 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____64528, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____64559 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____64559
      then true
      else
        (let uu____64566 = unfold_ty t  in
         match uu____64566 with
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
            let uu____64589 =
              let uu____64596 = eraseTypeDeep unfold_ty tyd  in
              let uu____64597 = eraseTypeDeep unfold_ty tycd  in
              (uu____64596, etag, uu____64597)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____64589
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____64606 = erasableType unfold_ty t  in
          if uu____64606
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____64611 =
               let uu____64618 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____64618, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____64611)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____64626 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____64626
      | uu____64629 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____64640 =
    let uu____64645 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____64645  in
  FStar_All.pipe_left uu____64640
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
          let uu____64733 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____64733
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____64749 = FStar_Range.file_of_range r  in (line, uu____64749)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64772,b) ->
        let uu____64774 = doms_and_cod b  in
        (match uu____64774 with | (ds,c) -> ((a :: ds), c))
    | uu____64795 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____64808 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____64808
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____64836,b) ->
        let uu____64838 = uncurry_mlty_fun b  in
        (match uu____64838 with | (args,res) -> ((a :: args), res))
    | uu____64859 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____64875 -> true
    | uu____64878 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____64888 -> uu____64888
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____64910 =
          let uu____64916 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____64916)  in
        FStar_Errors.log_issue r uu____64910
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____64929 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____64940 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____64951 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____64962 -> false
  
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
              let uu____65033 =
                let uu____65034 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65034  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65033
               in
            let lid_to_top_name l =
              let uu____65041 =
                let uu____65042 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____65042  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65041
               in
            let str_to_name s =
              let uu____65051 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____65051  in
            let str_to_top_name s =
              let uu____65060 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____65060  in
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
              let uu____65098 =
                let uu____65099 =
                  let uu____65106 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____65108 =
                    let uu____65111 =
                      let uu____65112 =
                        let uu____65113 =
                          let uu____65114 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____65114
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____65113  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____65112
                       in
                    [uu____65111]  in
                  (uu____65106, uu____65108)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65099  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____65098
               in
            let emb_prefix uu___621_65129 =
              match uu___621_65129 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____65143 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____65154 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____65183 =
                let uu____65185 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____65185  in
              emb_prefix l uu____65183  in
            let mk_any_embedding l s =
              let uu____65201 =
                let uu____65202 =
                  let uu____65209 = emb_prefix l "mk_any_emb"  in
                  let uu____65211 =
                    let uu____65214 = str_to_name s  in [uu____65214]  in
                  (uu____65209, uu____65211)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65202  in
              FStar_All.pipe_left w uu____65201  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____65264 =
                let uu____65265 =
                  let uu____65272 = emb_prefix l "e_arrow"  in
                  (uu____65272, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____65265  in
              FStar_All.pipe_left w uu____65264  in
            let known_type_constructors =
              let term_cs =
                let uu____65310 =
                  let uu____65325 =
                    let uu____65340 =
                      let uu____65355 =
                        let uu____65370 =
                          let uu____65385 =
                            let uu____65400 =
                              let uu____65415 =
                                let uu____65428 =
                                  let uu____65437 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____65437, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____65428, Syntax_term)  in
                              let uu____65451 =
                                let uu____65466 =
                                  let uu____65479 =
                                    let uu____65488 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____65488, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____65479, Refl_emb)  in
                                let uu____65502 =
                                  let uu____65517 =
                                    let uu____65530 =
                                      let uu____65539 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____65539, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____65530, Refl_emb)  in
                                  let uu____65553 =
                                    let uu____65568 =
                                      let uu____65581 =
                                        let uu____65590 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____65590, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____65581, Refl_emb)  in
                                    let uu____65604 =
                                      let uu____65619 =
                                        let uu____65632 =
                                          let uu____65641 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____65641,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____65632, Refl_emb)  in
                                      let uu____65655 =
                                        let uu____65670 =
                                          let uu____65683 =
                                            let uu____65692 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____65692,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____65683, Refl_emb)  in
                                        [uu____65670]  in
                                      uu____65619 :: uu____65655  in
                                    uu____65568 :: uu____65604  in
                                  uu____65517 :: uu____65553  in
                                uu____65466 :: uu____65502  in
                              uu____65415 :: uu____65451  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____65400
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____65385
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____65370
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____65355
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____65340
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____65325
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____65310
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_65999  ->
                     match uu___622_65999 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____66074 -> failwith "Impossible") term_cs
                 in
              fun uu___623_66100  ->
                match uu___623_66100 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____66115 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____66152  ->
                   match uu____66152 with
                   | ((x,args,uu____66168),uu____66169) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____66199 =
              match uu____66199 with
              | (bv',uu____66207) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____66241 =
                let uu____66242 = FStar_Syntax_Subst.compress t3  in
                uu____66242.FStar_Syntax_Syntax.n  in
              match uu____66241 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____66251 =
                    let uu____66253 =
                      let uu____66259 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____66259  in
                    FStar_Pervasives_Native.snd uu____66253  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____66251
              | FStar_Syntax_Syntax.Tm_refine (x,uu____66280) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____66286,uu____66287)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____66360 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____66360 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____66382 =
                           let uu____66383 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____66383  in
                         uu____66382.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____66401 = mk_embedding l env t0  in
                       let uu____66402 = mk_embedding l env t11  in
                       emb_arrow l uu____66401 uu____66402)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____66473 =
                      let uu____66480 =
                        let uu____66481 =
                          let uu____66496 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____66496)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____66481  in
                      FStar_Syntax_Syntax.mk uu____66480  in
                    uu____66473 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____66521 ->
                  let uu____66522 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66522 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66574 =
                         let uu____66575 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66575.FStar_Syntax_Syntax.n  in
                       (match uu____66574 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66601  ->
                                      match uu____66601 with
                                      | (t4,uu____66609) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66616 =
                              let uu____66629 =
                                FStar_Util.find_opt
                                  (fun uu____66661  ->
                                     match uu____66661 with
                                     | ((x,uu____66676,uu____66677),uu____66678)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66629
                                FStar_Util.must
                               in
                            (match uu____66616 with
                             | ((uu____66729,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _66746 when
                                      _66746 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____66751 ->
                            let uu____66752 =
                              let uu____66753 =
                                let uu____66755 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____66755
                                 in
                              NoTacticEmbedding uu____66753  in
                            FStar_Exn.raise uu____66752))
              | FStar_Syntax_Syntax.Tm_uinst uu____66758 ->
                  let uu____66765 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____66765 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____66817 =
                         let uu____66818 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____66818.FStar_Syntax_Syntax.n  in
                       (match uu____66817 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____66844  ->
                                      match uu____66844 with
                                      | (t4,uu____66852) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____66859 =
                              let uu____66872 =
                                FStar_Util.find_opt
                                  (fun uu____66904  ->
                                     match uu____66904 with
                                     | ((x,uu____66919,uu____66920),uu____66921)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____66872
                                FStar_Util.must
                               in
                            (match uu____66859 with
                             | ((uu____66972,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _66989 when
                                      _66989 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____66994 ->
                            let uu____66995 =
                              let uu____66996 =
                                let uu____66998 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____66998
                                 in
                              NoTacticEmbedding uu____66996  in
                            FStar_Exn.raise uu____66995))
              | FStar_Syntax_Syntax.Tm_app uu____67001 ->
                  let uu____67018 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____67018 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____67070 =
                         let uu____67071 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____67071.FStar_Syntax_Syntax.n  in
                       (match uu____67070 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____67097  ->
                                      match uu____67097 with
                                      | (t4,uu____67105) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____67112 =
                              let uu____67125 =
                                FStar_Util.find_opt
                                  (fun uu____67157  ->
                                     match uu____67157 with
                                     | ((x,uu____67172,uu____67173),uu____67174)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____67125
                                FStar_Util.must
                               in
                            (match uu____67112 with
                             | ((uu____67225,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _67242 when
                                      _67242 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____67247 ->
                            let uu____67248 =
                              let uu____67249 =
                                let uu____67251 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____67251
                                 in
                              NoTacticEmbedding uu____67249  in
                            FStar_Exn.raise uu____67248))
              | uu____67254 ->
                  let uu____67255 =
                    let uu____67256 =
                      let uu____67258 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____67258
                       in
                    NoTacticEmbedding uu____67256  in
                  FStar_Exn.raise uu____67255
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____67280 =
                      let uu____67281 =
                        let uu____67288 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67290 =
                          let uu____67293 =
                            let uu____67294 =
                              let uu____67295 =
                                let uu____67296 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67296
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67295
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67294
                             in
                          let uu____67298 =
                            let uu____67301 =
                              let uu____67302 =
                                let uu____67303 =
                                  let uu____67304 =
                                    let uu____67311 =
                                      let uu____67314 = str_to_name "args"
                                         in
                                      [uu____67314]  in
                                    (body, uu____67311)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____67304
                                   in
                                FStar_All.pipe_left w uu____67303  in
                              mk_lam "_" uu____67302  in
                            [uu____67301]  in
                          uu____67293 :: uu____67298  in
                        (uu____67288, uu____67290)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67281  in
                    FStar_All.pipe_left w uu____67280  in
                  mk_lam "args" body1
              | uu____67322 ->
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
                    let uu____67371 =
                      let uu____67372 =
                        let uu____67373 =
                          let uu____67380 =
                            let uu____67383 = str_to_name "args"  in
                            [uu____67383]  in
                          (body, uu____67380)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67373  in
                      FStar_All.pipe_left w uu____67372  in
                    (pattern, FStar_Pervasives_Native.None, uu____67371)  in
                  let default_branch =
                    let uu____67398 =
                      let uu____67399 =
                        let uu____67400 =
                          let uu____67407 = str_to_name "failwith"  in
                          let uu____67409 =
                            let uu____67412 =
                              let uu____67413 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____67413  in
                            [uu____67412]  in
                          (uu____67407, uu____67409)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____67400  in
                      FStar_All.pipe_left w uu____67399  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____67398)
                     in
                  let body1 =
                    let uu____67421 =
                      let uu____67422 =
                        let uu____67437 = str_to_name "args"  in
                        (uu____67437, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____67422  in
                    FStar_All.pipe_left w uu____67421  in
                  let body2 =
                    let uu____67474 =
                      let uu____67475 =
                        let uu____67482 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____67484 =
                          let uu____67487 =
                            let uu____67488 =
                              let uu____67489 =
                                let uu____67490 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____67490
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____67489
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____67488
                             in
                          let uu____67492 =
                            let uu____67495 = mk_lam "_" body1  in
                            [uu____67495]  in
                          uu____67487 :: uu____67492  in
                        (uu____67482, uu____67484)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____67475  in
                    FStar_All.pipe_left w uu____67474  in
                  mk_lam "args" body2
               in
            let uu____67500 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____67500 with
            | (bs,c) ->
                let uu____67533 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____67626 = FStar_Util.first_N n1 bs  in
                           match uu____67626 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____67704 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____67704
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____67721 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____67723 = FStar_Util.string_of_int n1
                                in
                             let uu____67725 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____67721 uu____67723 uu____67725
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____67533 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____67776 =
                       let uu____67797 =
                         FStar_Util.prefix_until
                           (fun uu____67839  ->
                              match uu____67839 with
                              | (b,uu____67848) ->
                                  let uu____67853 =
                                    let uu____67854 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____67854.FStar_Syntax_Syntax.n  in
                                  (match uu____67853 with
                                   | FStar_Syntax_Syntax.Tm_type uu____67858
                                       -> false
                                   | uu____67860 -> true)) bs1
                          in
                       match uu____67797 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____67776 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____68102 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____68102) type_vars
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
                                let uu____68202 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____68202
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____68219 =
                                      let uu____68222 =
                                        let uu____68225 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____68226 =
                                          let uu____68229 =
                                            let uu____68230 =
                                              let uu____68231 =
                                                let uu____68232 =
                                                  let uu____68244 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____68244,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____68232
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____68231
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____68230
                                             in
                                          [uu____68229; fv_lid_embedded; cb]
                                           in
                                        uu____68225 :: uu____68226  in
                                      res_embedding :: uu____68222  in
                                    FStar_List.append arg_unembeddings
                                      uu____68219
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
                                  let uu____68263 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____68263, arity, true)
                                else
                                  (let uu____68273 =
                                     let uu____68275 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____68275
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____68273
                                   then
                                     let h =
                                       let uu____68286 =
                                         let uu____68288 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____68288
                                          in
                                       str_to_top_name uu____68286  in
                                     let tac_fun =
                                       let uu____68291 =
                                         let uu____68292 =
                                           let uu____68299 =
                                             let uu____68300 =
                                               let uu____68302 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____68302
                                                in
                                             str_to_top_name uu____68300  in
                                           let uu____68304 =
                                             let uu____68307 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____68307]  in
                                           (uu____68299, uu____68304)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____68292
                                          in
                                       FStar_All.pipe_left w uu____68291  in
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
                                           let uu____68321 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____68321
                                       | uu____68325 ->
                                           let uu____68329 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____68329
                                        in
                                     let uu____68332 =
                                       let uu____68333 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____68333  in
                                     (uu____68332,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____68342 =
                                        let uu____68343 =
                                          let uu____68345 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____68345
                                           in
                                        NoTacticEmbedding uu____68343  in
                                      FStar_Exn.raise uu____68342))
                            | (b,uu____68357)::bs4 ->
                                let uu____68377 =
                                  let uu____68380 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____68380 :: accum_embeddings  in
                                aux loc uu____68377 bs4
                             in
                          (try
                             (fun uu___1304_68402  ->
                                match () with
                                | () ->
                                    let uu____68415 = aux Syntax_term [] bs2
                                       in
                                    (match uu____68415 with
                                     | (w1,a,b) ->
                                         let uu____68443 = aux NBE_t [] bs2
                                            in
                                         (match uu____68443 with
                                          | (w',uu____68465,uu____68466) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____68502 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____68502 msg);
                                FStar_Pervasives_Native.None))))
  