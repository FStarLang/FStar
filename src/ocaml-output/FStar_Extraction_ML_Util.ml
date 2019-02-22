open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____67808  ->
    let uu____67809 = FStar_Options.codegen ()  in
    uu____67809 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____67878 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____67908) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____67914) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____67919 ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____67923 ->
        failwith "Unhandled constant: reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_67937  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_67940 ->
          let uu____67941 =
            let uu____67943 = FStar_Range.string_of_range p  in
            let uu____67945 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____67943 uu____67945
             in
          failwith uu____67941
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____67962 =
        let uu____67963 =
          let uu____67964 =
            let uu____67976 = FStar_Util.string_of_int i  in
            (uu____67976, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____67964  in
        FStar_All.pipe_right uu____67963
          (fun _67989  -> FStar_Extraction_ML_Syntax.MLE_Const _67989)
         in
      FStar_All.pipe_right uu____67962
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____67998 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _67999  -> FStar_Extraction_ML_Syntax.MLE_Const _67999)
         in
      FStar_All.pipe_right uu____67998
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____68000 =
      let uu____68007 =
        let uu____68010 =
          let uu____68011 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____68011 cstr  in
        let uu____68014 =
          let uu____68017 =
            let uu____68018 =
              let uu____68020 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____68020 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____68018 cint  in
          let uu____68023 =
            let uu____68026 =
              let uu____68027 =
                let uu____68029 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____68029 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____68027 cint  in
            let uu____68032 =
              let uu____68035 =
                let uu____68036 =
                  let uu____68038 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____68038 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____68036 cint  in
              let uu____68041 =
                let uu____68044 =
                  let uu____68045 =
                    let uu____68047 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____68047 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____68045 cint  in
                [uu____68044]  in
              uu____68035 :: uu____68041  in
            uu____68026 :: uu____68032  in
          uu____68017 :: uu____68023  in
        uu____68010 :: uu____68014  in
      (mk_range_mle, uu____68007)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____68000
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____68064 ->
          let uu____68065 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____68065
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____68093 =
            FStar_Util.find_opt
              (fun uu____68109  ->
                 match uu____68109 with | (y,uu____68117) -> y = x) subst1
             in
          (match uu____68093 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____68141 =
            let uu____68148 = subst_aux subst1 t1  in
            let uu____68149 = subst_aux subst1 t2  in
            (uu____68148, f, uu____68149)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____68141
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____68156 =
            let uu____68163 = FStar_List.map (subst_aux subst1) args  in
            (uu____68163, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____68156
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____68171 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____68171
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____68187  ->
    fun args  ->
      match uu____68187 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____68201 =
               let uu____68202 = FStar_List.zip formals args  in
               subst_aux uu____68202 t  in
             FStar_Pervasives_Native.Some uu____68201)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____68234 = try_subst ts args  in
      match uu____68234 with
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
    fun uu___617_68251  ->
      match uu___617_68251 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____68260 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____68260 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____68266 = try_subst ts args  in
               (match uu____68266 with
                | FStar_Pervasives_Native.None  ->
                    let uu____68271 =
                      let uu____68273 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____68275 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____68277 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____68273 uu____68275 uu____68277
                       in
                    failwith uu____68271
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____68284 -> FStar_Pervasives_Native.None)
      | uu____68287 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____68301) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____68305 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_68317  ->
    match uu___618_68317 with
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
        | uu____68338 ->
            let uu____68343 =
              let uu____68345 = FStar_Range.string_of_range r  in
              let uu____68347 = eff_to_string f  in
              let uu____68349 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____68345
                uu____68347 uu____68349
               in
            failwith uu____68343
  
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
    (fun uu____68392  ->
       fun t  ->
         match uu____68392 with
         | (uu____68399,t0) ->
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
                | uu____68527 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____68564 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____68572 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____68572 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____68583;
                     FStar_Extraction_ML_Syntax.loc = uu____68584;_}
                   ->
                   let uu____68609 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____68609
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____68630 = type_leq unfold_ty t2 t2'  in
                        (if uu____68630
                         then
                           let body1 =
                             let uu____68644 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____68644
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____68652 =
                             let uu____68655 =
                               let uu____68656 =
                                 let uu____68661 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____68661
                                  in
                               FStar_All.pipe_left uu____68656
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____68655  in
                           (true, uu____68652)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____68701 =
                           let uu____68709 =
                             let uu____68712 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _68715  ->
                                  FStar_Pervasives_Native.Some _68715)
                               uu____68712
                              in
                           type_leq_c unfold_ty uu____68709 t2 t2'  in
                         match uu____68701 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____68740 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____68740
                               | uu____68751 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____68763 ->
                   let uu____68766 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____68766
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____68812 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____68812
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____68837 = unfold_ty t  in
                 match uu____68837 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____68852 = unfold_ty t'  in
                     (match uu____68852 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____68877 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____68877
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____68904,uu____68905)
              ->
              let uu____68912 = unfold_ty t  in
              (match uu____68912 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____68927 -> (false, FStar_Pervasives_Native.None))
          | (uu____68934,FStar_Extraction_ML_Syntax.MLTY_Named uu____68935)
              ->
              let uu____68942 = unfold_ty t'  in
              (match uu____68942 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____68957 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____68968 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____68983 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____68983 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____69014 =
          let uu____69021 = erase_effect_annotations t1  in
          let uu____69022 = erase_effect_annotations t2  in
          (uu____69021, FStar_Extraction_ML_Syntax.E_PURE, uu____69022)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____69014
    | uu____69023 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_69051  ->
    match uu___619_69051 with
    | (FStar_Util.Inl uu____69063,uu____69064)::uu____69065 -> true
    | uu____69089 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____69117  ->
    match uu____69117 with
    | (ns,n1) ->
        let uu____69139 =
          let uu____69141 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____69141  in
        if uu____69139
        then
          let uu____69151 =
            let uu____69153 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____69153  in
          FStar_Pervasives_Native.Some uu____69151
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____69172 = is_xtuple mlp  in
        (match uu____69172 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____69179 -> e)
    | uu____69183 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_69194  ->
    match uu___620_69194 with
    | f::uu____69201 ->
        let uu____69204 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____69204 with
         | (ns,uu____69215) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____69228 -> failwith "impos"
  
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
  fun uu____69294  ->
    match uu____69294 with
    | (ns,n1) ->
        let uu____69316 =
          let uu____69318 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____69318  in
        if uu____69316
        then
          let uu____69328 =
            let uu____69330 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____69330  in
          FStar_Pervasives_Native.Some uu____69328
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____69349 = is_xtuple_ty mlp  in
        (match uu____69349 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____69356 -> t)
    | uu____69360 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____69374 = codegen_fsharp ()  in
    if uu____69374
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____69396  ->
    match uu____69396 with
    | (ns,n1) ->
        let uu____69416 = codegen_fsharp ()  in
        if uu____69416
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____69444 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____69444, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____69478 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____69478
      then true
      else
        (let uu____69485 = unfold_ty t  in
         match uu____69485 with
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
            let uu____69515 =
              let uu____69522 = eraseTypeDeep unfold_ty tyd  in
              let uu____69526 = eraseTypeDeep unfold_ty tycd  in
              (uu____69522, etag, uu____69526)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____69515
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____69538 = erasableType unfold_ty t  in
          if uu____69538
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____69546 =
               let uu____69553 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____69553, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____69546)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____69564 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____69564
      | uu____69570 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____69581 =
    let uu____69586 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____69586  in
  FStar_All.pipe_left uu____69581
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
          let uu____69674 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____69674
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____69690 = FStar_Range.file_of_range r  in (line, uu____69690)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69713,b) ->
        let uu____69715 = doms_and_cod b  in
        (match uu____69715 with | (ds,c) -> ((a :: ds), c))
    | uu____69736 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____69749 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____69749
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69777,b) ->
        let uu____69779 = uncurry_mlty_fun b  in
        (match uu____69779 with | (args,res) -> ((a :: args), res))
    | uu____69800 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____69816 -> true
    | uu____69819 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____69830 -> uu____69830
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____69852 =
          let uu____69858 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____69858)  in
        FStar_Errors.log_issue r uu____69852
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____69871 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____69882 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____69893 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____69904 -> false
  
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
              let uu____69975 =
                let uu____69976 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____69976  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____69975
               in
            let lid_to_top_name l =
              let uu____69983 =
                let uu____69984 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____69984  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____69983
               in
            let str_to_name s =
              let uu____69993 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____69993  in
            let str_to_top_name s =
              let uu____70002 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____70002  in
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
              let uu____70040 =
                let uu____70041 =
                  let uu____70048 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____70050 =
                    let uu____70053 =
                      let uu____70054 =
                        let uu____70055 =
                          let uu____70056 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____70056
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____70055  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____70054
                       in
                    [uu____70053]  in
                  (uu____70048, uu____70050)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70041  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70040
               in
            let emb_prefix uu___621_70071 =
              match uu___621_70071 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____70085 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____70096 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____70125 =
                let uu____70127 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____70127  in
              emb_prefix l uu____70125  in
            let mk_any_embedding l s =
              let uu____70143 =
                let uu____70144 =
                  let uu____70151 = emb_prefix l "mk_any_emb"  in
                  let uu____70153 =
                    let uu____70156 = str_to_name s  in [uu____70156]  in
                  (uu____70151, uu____70153)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70144  in
              FStar_All.pipe_left w uu____70143  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____70206 =
                let uu____70207 =
                  let uu____70214 = emb_prefix l "e_arrow"  in
                  (uu____70214, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70207  in
              FStar_All.pipe_left w uu____70206  in
            let known_type_constructors =
              let term_cs =
                let uu____70252 =
                  let uu____70267 =
                    let uu____70282 =
                      let uu____70297 =
                        let uu____70312 =
                          let uu____70327 =
                            let uu____70342 =
                              let uu____70357 =
                                let uu____70370 =
                                  let uu____70379 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____70379, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____70370, Syntax_term)  in
                              let uu____70393 =
                                let uu____70408 =
                                  let uu____70421 =
                                    let uu____70430 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____70430, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____70421, Refl_emb)  in
                                let uu____70444 =
                                  let uu____70459 =
                                    let uu____70472 =
                                      let uu____70481 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____70481, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____70472, Refl_emb)  in
                                  let uu____70495 =
                                    let uu____70510 =
                                      let uu____70523 =
                                        let uu____70532 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____70532, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____70523, Refl_emb)  in
                                    let uu____70546 =
                                      let uu____70561 =
                                        let uu____70574 =
                                          let uu____70583 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____70583,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____70574, Refl_emb)  in
                                      let uu____70597 =
                                        let uu____70612 =
                                          let uu____70625 =
                                            let uu____70634 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____70634,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____70625, Refl_emb)  in
                                        [uu____70612]  in
                                      uu____70561 :: uu____70597  in
                                    uu____70510 :: uu____70546  in
                                  uu____70459 :: uu____70495  in
                                uu____70408 :: uu____70444  in
                              uu____70357 :: uu____70393  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____70342
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____70327
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____70312
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____70297
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____70282
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____70267
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____70252
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_70941  ->
                     match uu___622_70941 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____71016 -> failwith "Impossible") term_cs
                 in
              fun uu___623_71042  ->
                match uu___623_71042 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____71057 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____71094  ->
                   match uu____71094 with
                   | ((x,args,uu____71110),uu____71111) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____71141 =
              match uu____71141 with
              | (bv',uu____71149) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____71183 =
                let uu____71184 = FStar_Syntax_Subst.compress t3  in
                uu____71184.FStar_Syntax_Syntax.n  in
              match uu____71183 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____71193 =
                    let uu____71195 =
                      let uu____71201 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____71201  in
                    FStar_Pervasives_Native.snd uu____71195  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____71193
              | FStar_Syntax_Syntax.Tm_refine (x,uu____71222) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____71228,uu____71229)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____71302 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____71302 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____71324 =
                           let uu____71325 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____71325  in
                         uu____71324.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____71343 = mk_embedding l env t0  in
                       let uu____71344 = mk_embedding l env t11  in
                       emb_arrow l uu____71343 uu____71344)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____71415 =
                      let uu____71422 =
                        let uu____71423 =
                          let uu____71438 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____71438)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____71423  in
                      FStar_Syntax_Syntax.mk uu____71422  in
                    uu____71415 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____71466 ->
                  let uu____71467 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71467 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71519 =
                         let uu____71520 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71520.FStar_Syntax_Syntax.n  in
                       (match uu____71519 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71550  ->
                                      match uu____71550 with
                                      | (t4,uu____71558) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71565 =
                              let uu____71578 =
                                FStar_Util.find_opt
                                  (fun uu____71610  ->
                                     match uu____71610 with
                                     | ((x,uu____71625,uu____71626),uu____71627)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71578
                                FStar_Util.must
                               in
                            (match uu____71565 with
                             | ((uu____71678,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _71695 when
                                      _71695 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____71700 ->
                            let uu____71701 =
                              let uu____71702 =
                                let uu____71704 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____71704
                                 in
                              NoTacticEmbedding uu____71702  in
                            FStar_Exn.raise uu____71701))
              | FStar_Syntax_Syntax.Tm_uinst uu____71707 ->
                  let uu____71714 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71714 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71766 =
                         let uu____71767 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71767.FStar_Syntax_Syntax.n  in
                       (match uu____71766 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71797  ->
                                      match uu____71797 with
                                      | (t4,uu____71805) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71812 =
                              let uu____71825 =
                                FStar_Util.find_opt
                                  (fun uu____71857  ->
                                     match uu____71857 with
                                     | ((x,uu____71872,uu____71873),uu____71874)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71825
                                FStar_Util.must
                               in
                            (match uu____71812 with
                             | ((uu____71925,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _71942 when
                                      _71942 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____71947 ->
                            let uu____71948 =
                              let uu____71949 =
                                let uu____71951 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____71951
                                 in
                              NoTacticEmbedding uu____71949  in
                            FStar_Exn.raise uu____71948))
              | FStar_Syntax_Syntax.Tm_app uu____71954 ->
                  let uu____71971 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71971 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____72023 =
                         let uu____72024 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____72024.FStar_Syntax_Syntax.n  in
                       (match uu____72023 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____72054  ->
                                      match uu____72054 with
                                      | (t4,uu____72062) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____72069 =
                              let uu____72082 =
                                FStar_Util.find_opt
                                  (fun uu____72114  ->
                                     match uu____72114 with
                                     | ((x,uu____72129,uu____72130),uu____72131)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____72082
                                FStar_Util.must
                               in
                            (match uu____72069 with
                             | ((uu____72182,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72199 when
                                      _72199 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72204 ->
                            let uu____72205 =
                              let uu____72206 =
                                let uu____72208 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72208
                                 in
                              NoTacticEmbedding uu____72206  in
                            FStar_Exn.raise uu____72205))
              | uu____72211 ->
                  let uu____72212 =
                    let uu____72213 =
                      let uu____72215 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____72215
                       in
                    NoTacticEmbedding uu____72213  in
                  FStar_Exn.raise uu____72212
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____72237 =
                      let uu____72238 =
                        let uu____72245 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72247 =
                          let uu____72250 =
                            let uu____72251 =
                              let uu____72252 =
                                let uu____72253 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72253
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72252
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72251
                             in
                          let uu____72255 =
                            let uu____72258 =
                              let uu____72259 =
                                let uu____72260 =
                                  let uu____72261 =
                                    let uu____72268 =
                                      let uu____72271 = str_to_name "args"
                                         in
                                      [uu____72271]  in
                                    (body, uu____72268)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____72261
                                   in
                                FStar_All.pipe_left w uu____72260  in
                              mk_lam "_" uu____72259  in
                            [uu____72258]  in
                          uu____72250 :: uu____72255  in
                        (uu____72245, uu____72247)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72238  in
                    FStar_All.pipe_left w uu____72237  in
                  mk_lam "args" body1
              | uu____72279 ->
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
                    let uu____72328 =
                      let uu____72329 =
                        let uu____72330 =
                          let uu____72337 =
                            let uu____72340 = str_to_name "args"  in
                            [uu____72340]  in
                          (body, uu____72337)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72330  in
                      FStar_All.pipe_left w uu____72329  in
                    (pattern, FStar_Pervasives_Native.None, uu____72328)  in
                  let default_branch =
                    let uu____72355 =
                      let uu____72356 =
                        let uu____72357 =
                          let uu____72364 = str_to_name "failwith"  in
                          let uu____72366 =
                            let uu____72369 =
                              let uu____72370 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____72370  in
                            [uu____72369]  in
                          (uu____72364, uu____72366)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72357  in
                      FStar_All.pipe_left w uu____72356  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____72355)
                     in
                  let body1 =
                    let uu____72378 =
                      let uu____72379 =
                        let uu____72394 = str_to_name "args"  in
                        (uu____72394, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____72379  in
                    FStar_All.pipe_left w uu____72378  in
                  let body2 =
                    let uu____72431 =
                      let uu____72432 =
                        let uu____72439 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72441 =
                          let uu____72444 =
                            let uu____72445 =
                              let uu____72446 =
                                let uu____72447 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72447
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72446
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72445
                             in
                          let uu____72449 =
                            let uu____72452 = mk_lam "_" body1  in
                            [uu____72452]  in
                          uu____72444 :: uu____72449  in
                        (uu____72439, uu____72441)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72432  in
                    FStar_All.pipe_left w uu____72431  in
                  mk_lam "args" body2
               in
            let uu____72457 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____72457 with
            | (bs,c) ->
                let uu____72490 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____72591 = FStar_Util.first_N n1 bs  in
                           match uu____72591 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____72669 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____72669
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____72686 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____72688 = FStar_Util.string_of_int n1
                                in
                             let uu____72690 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____72686 uu____72688 uu____72690
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____72490 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____72747 =
                       let uu____72768 =
                         FStar_Util.prefix_until
                           (fun uu____72810  ->
                              match uu____72810 with
                              | (b,uu____72819) ->
                                  let uu____72824 =
                                    let uu____72825 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____72825.FStar_Syntax_Syntax.n  in
                                  (match uu____72824 with
                                   | FStar_Syntax_Syntax.Tm_type uu____72829
                                       -> false
                                   | uu____72831 -> true)) bs1
                          in
                       match uu____72768 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____72747 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____73073 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____73073) type_vars
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
                                let uu____73173 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____73173
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____73194 =
                                      let uu____73197 =
                                        let uu____73200 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____73201 =
                                          let uu____73204 =
                                            let uu____73205 =
                                              let uu____73206 =
                                                let uu____73207 =
                                                  let uu____73219 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____73219,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____73207
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____73206
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____73205
                                             in
                                          [uu____73204; fv_lid_embedded; cb]
                                           in
                                        uu____73200 :: uu____73201  in
                                      res_embedding :: uu____73197  in
                                    FStar_List.append arg_unembeddings
                                      uu____73194
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
                                  let uu____73244 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____73244, arity, true)
                                else
                                  (let uu____73258 =
                                     let uu____73260 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____73260
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____73258
                                   then
                                     let h =
                                       let uu____73271 =
                                         let uu____73273 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____73273
                                          in
                                       str_to_top_name uu____73271  in
                                     let tac_fun =
                                       let uu____73282 =
                                         let uu____73283 =
                                           let uu____73290 =
                                             let uu____73291 =
                                               let uu____73293 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____73293
                                                in
                                             str_to_top_name uu____73291  in
                                           let uu____73301 =
                                             let uu____73304 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____73304]  in
                                           (uu____73290, uu____73301)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____73283
                                          in
                                       FStar_All.pipe_left w uu____73282  in
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
                                           let uu____73318 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____73318
                                       | uu____73322 ->
                                           let uu____73326 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____73326
                                        in
                                     let uu____73329 =
                                       let uu____73330 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____73330  in
                                     (uu____73329,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____73345 =
                                        let uu____73346 =
                                          let uu____73348 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____73348
                                           in
                                        NoTacticEmbedding uu____73346  in
                                      FStar_Exn.raise uu____73345))
                            | (b,uu____73360)::bs4 ->
                                let uu____73380 =
                                  let uu____73383 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____73383 :: accum_embeddings  in
                                aux loc uu____73380 bs4
                             in
                          (try
                             (fun uu___1304_73405  ->
                                match () with
                                | () ->
                                    let uu____73418 = aux Syntax_term [] bs2
                                       in
                                    (match uu____73418 with
                                     | (w1,a,b) ->
                                         let uu____73446 = aux NBE_t [] bs2
                                            in
                                         (match uu____73446 with
                                          | (w',uu____73468,uu____73469) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____73505 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____73505 msg);
                                FStar_Pervasives_Native.None))))
  