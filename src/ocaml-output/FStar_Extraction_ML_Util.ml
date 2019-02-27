open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____67818  ->
    let uu____67819 = FStar_Options.codegen ()  in
    uu____67819 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____67888 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____67918) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____67924) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____67929 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____67933 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_67947  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_67950 ->
          let uu____67951 =
            let uu____67953 = FStar_Range.string_of_range p  in
            let uu____67955 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____67953 uu____67955
             in
          failwith uu____67951
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____67972 =
        let uu____67973 =
          let uu____67974 =
            let uu____67986 = FStar_Util.string_of_int i  in
            (uu____67986, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____67974  in
        FStar_All.pipe_right uu____67973
          (fun _67999  -> FStar_Extraction_ML_Syntax.MLE_Const _67999)
         in
      FStar_All.pipe_right uu____67972
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____68008 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _68009  -> FStar_Extraction_ML_Syntax.MLE_Const _68009)
         in
      FStar_All.pipe_right uu____68008
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____68010 =
      let uu____68017 =
        let uu____68020 =
          let uu____68021 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____68021 cstr  in
        let uu____68024 =
          let uu____68027 =
            let uu____68028 =
              let uu____68030 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____68030 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____68028 cint  in
          let uu____68033 =
            let uu____68036 =
              let uu____68037 =
                let uu____68039 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____68039 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____68037 cint  in
            let uu____68042 =
              let uu____68045 =
                let uu____68046 =
                  let uu____68048 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____68048 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____68046 cint  in
              let uu____68051 =
                let uu____68054 =
                  let uu____68055 =
                    let uu____68057 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____68057 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____68055 cint  in
                [uu____68054]  in
              uu____68045 :: uu____68051  in
            uu____68036 :: uu____68042  in
          uu____68027 :: uu____68033  in
        uu____68020 :: uu____68024  in
      (mk_range_mle, uu____68017)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____68010
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____68074 ->
          let uu____68075 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____68075
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____68103 =
            FStar_Util.find_opt
              (fun uu____68119  ->
                 match uu____68119 with | (y,uu____68127) -> y = x) subst1
             in
          (match uu____68103 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____68151 =
            let uu____68158 = subst_aux subst1 t1  in
            let uu____68159 = subst_aux subst1 t2  in
            (uu____68158, f, uu____68159)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____68151
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____68166 =
            let uu____68173 = FStar_List.map (subst_aux subst1) args  in
            (uu____68173, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____68166
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____68181 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____68181
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____68197  ->
    fun args  ->
      match uu____68197 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____68211 =
               let uu____68212 = FStar_List.zip formals args  in
               subst_aux uu____68212 t  in
             FStar_Pervasives_Native.Some uu____68211)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____68244 = try_subst ts args  in
      match uu____68244 with
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
    fun uu___617_68261  ->
      match uu___617_68261 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____68270 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____68270 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____68276 = try_subst ts args  in
               (match uu____68276 with
                | FStar_Pervasives_Native.None  ->
                    let uu____68281 =
                      let uu____68283 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____68285 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____68287 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____68283 uu____68285 uu____68287
                       in
                    failwith uu____68281
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____68294 -> FStar_Pervasives_Native.None)
      | uu____68297 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____68311) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____68315 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_68327  ->
    match uu___618_68327 with
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
        | uu____68348 ->
            let uu____68353 =
              let uu____68355 = FStar_Range.string_of_range r  in
              let uu____68357 = eff_to_string f  in
              let uu____68359 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____68355
                uu____68357 uu____68359
               in
            failwith uu____68353
  
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
    (fun uu____68402  ->
       fun t  ->
         match uu____68402 with
         | (uu____68409,t0) ->
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
                | uu____68537 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____68574 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____68582 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____68582 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____68593;
                     FStar_Extraction_ML_Syntax.loc = uu____68594;_}
                   ->
                   let uu____68619 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____68619
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____68640 = type_leq unfold_ty t2 t2'  in
                        (if uu____68640
                         then
                           let body1 =
                             let uu____68654 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____68654
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____68662 =
                             let uu____68665 =
                               let uu____68666 =
                                 let uu____68671 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____68671
                                  in
                               FStar_All.pipe_left uu____68666
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____68665  in
                           (true, uu____68662)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____68711 =
                           let uu____68719 =
                             let uu____68722 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _68725  ->
                                  FStar_Pervasives_Native.Some _68725)
                               uu____68722
                              in
                           type_leq_c unfold_ty uu____68719 t2 t2'  in
                         match uu____68711 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____68750 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____68750
                               | uu____68761 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____68773 ->
                   let uu____68776 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____68776
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____68822 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____68822
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____68847 = unfold_ty t  in
                 match uu____68847 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____68862 = unfold_ty t'  in
                     (match uu____68862 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____68887 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____68887
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____68914,uu____68915)
              ->
              let uu____68922 = unfold_ty t  in
              (match uu____68922 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____68937 -> (false, FStar_Pervasives_Native.None))
          | (uu____68944,FStar_Extraction_ML_Syntax.MLTY_Named uu____68945)
              ->
              let uu____68952 = unfold_ty t'  in
              (match uu____68952 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____68967 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____68978 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____68993 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____68993 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____69024 =
          let uu____69031 = erase_effect_annotations t1  in
          let uu____69032 = erase_effect_annotations t2  in
          (uu____69031, FStar_Extraction_ML_Syntax.E_PURE, uu____69032)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____69024
    | uu____69033 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_69061  ->
    match uu___619_69061 with
    | (FStar_Util.Inl uu____69073,uu____69074)::uu____69075 -> true
    | uu____69099 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____69127  ->
    match uu____69127 with
    | (ns,n1) ->
        let uu____69149 =
          let uu____69151 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____69151  in
        if uu____69149
        then
          let uu____69161 =
            let uu____69163 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____69163  in
          FStar_Pervasives_Native.Some uu____69161
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____69182 = is_xtuple mlp  in
        (match uu____69182 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____69189 -> e)
    | uu____69193 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_69204  ->
    match uu___620_69204 with
    | f::uu____69211 ->
        let uu____69214 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____69214 with
         | (ns,uu____69225) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____69238 -> failwith "impos"
  
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
  fun uu____69304  ->
    match uu____69304 with
    | (ns,n1) ->
        let uu____69326 =
          let uu____69328 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____69328  in
        if uu____69326
        then
          let uu____69338 =
            let uu____69340 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____69340  in
          FStar_Pervasives_Native.Some uu____69338
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____69359 = is_xtuple_ty mlp  in
        (match uu____69359 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____69366 -> t)
    | uu____69370 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____69384 = codegen_fsharp ()  in
    if uu____69384
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____69406  ->
    match uu____69406 with
    | (ns,n1) ->
        let uu____69426 = codegen_fsharp ()  in
        if uu____69426
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____69454 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____69454, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____69488 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____69488
      then true
      else
        (let uu____69495 = unfold_ty t  in
         match uu____69495 with
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
            let uu____69525 =
              let uu____69532 = eraseTypeDeep unfold_ty tyd  in
              let uu____69536 = eraseTypeDeep unfold_ty tycd  in
              (uu____69532, etag, uu____69536)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____69525
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____69548 = erasableType unfold_ty t  in
          if uu____69548
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____69556 =
               let uu____69563 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____69563, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____69556)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____69574 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____69574
      | uu____69580 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____69591 =
    let uu____69596 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____69596  in
  FStar_All.pipe_left uu____69591
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
          let uu____69684 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____69684
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____69700 = FStar_Range.file_of_range r  in (line, uu____69700)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69723,b) ->
        let uu____69725 = doms_and_cod b  in
        (match uu____69725 with | (ds,c) -> ((a :: ds), c))
    | uu____69746 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____69759 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____69759
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69787,b) ->
        let uu____69789 = uncurry_mlty_fun b  in
        (match uu____69789 with | (args,res) -> ((a :: args), res))
    | uu____69810 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____69826 -> true
    | uu____69829 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____69840 -> uu____69840
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____69862 =
          let uu____69868 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____69868)  in
        FStar_Errors.log_issue r uu____69862
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____69881 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____69892 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____69903 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____69914 -> false
  
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
              let uu____69985 =
                let uu____69986 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____69986  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____69985
               in
            let lid_to_top_name l =
              let uu____69993 =
                let uu____69994 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____69994  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____69993
               in
            let str_to_name s =
              let uu____70003 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____70003  in
            let str_to_top_name s =
              let uu____70012 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____70012  in
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
              let uu____70050 =
                let uu____70051 =
                  let uu____70058 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____70060 =
                    let uu____70063 =
                      let uu____70064 =
                        let uu____70065 =
                          let uu____70066 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____70066
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____70065  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____70064
                       in
                    [uu____70063]  in
                  (uu____70058, uu____70060)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70051  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70050
               in
            let emb_prefix uu___621_70081 =
              match uu___621_70081 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____70095 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____70106 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____70135 =
                let uu____70137 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____70137  in
              emb_prefix l uu____70135  in
            let mk_any_embedding l s =
              let uu____70153 =
                let uu____70154 =
                  let uu____70161 = emb_prefix l "mk_any_emb"  in
                  let uu____70163 =
                    let uu____70166 = str_to_name s  in [uu____70166]  in
                  (uu____70161, uu____70163)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70154  in
              FStar_All.pipe_left w uu____70153  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____70216 =
                let uu____70217 =
                  let uu____70224 = emb_prefix l "e_arrow"  in
                  (uu____70224, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70217  in
              FStar_All.pipe_left w uu____70216  in
            let known_type_constructors =
              let term_cs =
                let uu____70262 =
                  let uu____70277 =
                    let uu____70292 =
                      let uu____70307 =
                        let uu____70322 =
                          let uu____70337 =
                            let uu____70352 =
                              let uu____70367 =
                                let uu____70380 =
                                  let uu____70389 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____70389, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____70380, Syntax_term)  in
                              let uu____70403 =
                                let uu____70418 =
                                  let uu____70431 =
                                    let uu____70440 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____70440, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____70431, Refl_emb)  in
                                let uu____70454 =
                                  let uu____70469 =
                                    let uu____70482 =
                                      let uu____70491 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____70491, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____70482, Refl_emb)  in
                                  let uu____70505 =
                                    let uu____70520 =
                                      let uu____70533 =
                                        let uu____70542 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____70542, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____70533, Refl_emb)  in
                                    let uu____70556 =
                                      let uu____70571 =
                                        let uu____70584 =
                                          let uu____70593 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____70593,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____70584, Refl_emb)  in
                                      let uu____70607 =
                                        let uu____70622 =
                                          let uu____70635 =
                                            let uu____70644 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____70644,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____70635, Refl_emb)  in
                                        [uu____70622]  in
                                      uu____70571 :: uu____70607  in
                                    uu____70520 :: uu____70556  in
                                  uu____70469 :: uu____70505  in
                                uu____70418 :: uu____70454  in
                              uu____70367 :: uu____70403  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____70352
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____70337
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____70322
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____70307
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____70292
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____70277
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____70262
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_70951  ->
                     match uu___622_70951 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____71026 -> failwith "Impossible") term_cs
                 in
              fun uu___623_71052  ->
                match uu___623_71052 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____71067 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____71104  ->
                   match uu____71104 with
                   | ((x,args,uu____71120),uu____71121) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____71151 =
              match uu____71151 with
              | (bv',uu____71159) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____71193 =
                let uu____71194 = FStar_Syntax_Subst.compress t3  in
                uu____71194.FStar_Syntax_Syntax.n  in
              match uu____71193 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____71203 =
                    let uu____71205 =
                      let uu____71211 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____71211  in
                    FStar_Pervasives_Native.snd uu____71205  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____71203
              | FStar_Syntax_Syntax.Tm_refine (x,uu____71232) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____71238,uu____71239)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____71312 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____71312 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____71334 =
                           let uu____71335 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____71335  in
                         uu____71334.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____71353 = mk_embedding l env t0  in
                       let uu____71354 = mk_embedding l env t11  in
                       emb_arrow l uu____71353 uu____71354)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____71425 =
                      let uu____71432 =
                        let uu____71433 =
                          let uu____71448 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____71448)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____71433  in
                      FStar_Syntax_Syntax.mk uu____71432  in
                    uu____71425 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____71476 ->
                  let uu____71477 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71477 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71529 =
                         let uu____71530 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71530.FStar_Syntax_Syntax.n  in
                       (match uu____71529 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71560  ->
                                      match uu____71560 with
                                      | (t4,uu____71568) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71575 =
                              let uu____71588 =
                                FStar_Util.find_opt
                                  (fun uu____71620  ->
                                     match uu____71620 with
                                     | ((x,uu____71635,uu____71636),uu____71637)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71588
                                FStar_Util.must
                               in
                            (match uu____71575 with
                             | ((uu____71688,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _71705 when
                                      _71705 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____71710 ->
                            let uu____71711 =
                              let uu____71712 =
                                let uu____71714 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____71714
                                 in
                              NoTacticEmbedding uu____71712  in
                            FStar_Exn.raise uu____71711))
              | FStar_Syntax_Syntax.Tm_uinst uu____71717 ->
                  let uu____71724 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71724 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71776 =
                         let uu____71777 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71777.FStar_Syntax_Syntax.n  in
                       (match uu____71776 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71807  ->
                                      match uu____71807 with
                                      | (t4,uu____71815) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71822 =
                              let uu____71835 =
                                FStar_Util.find_opt
                                  (fun uu____71867  ->
                                     match uu____71867 with
                                     | ((x,uu____71882,uu____71883),uu____71884)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71835
                                FStar_Util.must
                               in
                            (match uu____71822 with
                             | ((uu____71935,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _71952 when
                                      _71952 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____71957 ->
                            let uu____71958 =
                              let uu____71959 =
                                let uu____71961 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____71961
                                 in
                              NoTacticEmbedding uu____71959  in
                            FStar_Exn.raise uu____71958))
              | FStar_Syntax_Syntax.Tm_app uu____71964 ->
                  let uu____71981 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71981 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____72033 =
                         let uu____72034 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____72034.FStar_Syntax_Syntax.n  in
                       (match uu____72033 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____72064  ->
                                      match uu____72064 with
                                      | (t4,uu____72072) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____72079 =
                              let uu____72092 =
                                FStar_Util.find_opt
                                  (fun uu____72124  ->
                                     match uu____72124 with
                                     | ((x,uu____72139,uu____72140),uu____72141)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____72092
                                FStar_Util.must
                               in
                            (match uu____72079 with
                             | ((uu____72192,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72209 when
                                      _72209 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72214 ->
                            let uu____72215 =
                              let uu____72216 =
                                let uu____72218 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72218
                                 in
                              NoTacticEmbedding uu____72216  in
                            FStar_Exn.raise uu____72215))
              | uu____72221 ->
                  let uu____72222 =
                    let uu____72223 =
                      let uu____72225 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____72225
                       in
                    NoTacticEmbedding uu____72223  in
                  FStar_Exn.raise uu____72222
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____72247 =
                      let uu____72248 =
                        let uu____72255 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72257 =
                          let uu____72260 =
                            let uu____72261 =
                              let uu____72262 =
                                let uu____72263 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72263
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72262
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72261
                             in
                          let uu____72265 =
                            let uu____72268 =
                              let uu____72269 =
                                let uu____72270 =
                                  let uu____72271 =
                                    let uu____72278 =
                                      let uu____72281 = str_to_name "args"
                                         in
                                      [uu____72281]  in
                                    (body, uu____72278)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____72271
                                   in
                                FStar_All.pipe_left w uu____72270  in
                              mk_lam "_" uu____72269  in
                            [uu____72268]  in
                          uu____72260 :: uu____72265  in
                        (uu____72255, uu____72257)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72248  in
                    FStar_All.pipe_left w uu____72247  in
                  mk_lam "args" body1
              | uu____72289 ->
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
                    let uu____72338 =
                      let uu____72339 =
                        let uu____72340 =
                          let uu____72347 =
                            let uu____72350 = str_to_name "args"  in
                            [uu____72350]  in
                          (body, uu____72347)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72340  in
                      FStar_All.pipe_left w uu____72339  in
                    (pattern, FStar_Pervasives_Native.None, uu____72338)  in
                  let default_branch =
                    let uu____72365 =
                      let uu____72366 =
                        let uu____72367 =
                          let uu____72374 = str_to_name "failwith"  in
                          let uu____72376 =
                            let uu____72379 =
                              let uu____72380 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____72380  in
                            [uu____72379]  in
                          (uu____72374, uu____72376)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72367  in
                      FStar_All.pipe_left w uu____72366  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____72365)
                     in
                  let body1 =
                    let uu____72388 =
                      let uu____72389 =
                        let uu____72404 = str_to_name "args"  in
                        (uu____72404, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____72389  in
                    FStar_All.pipe_left w uu____72388  in
                  let body2 =
                    let uu____72441 =
                      let uu____72442 =
                        let uu____72449 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72451 =
                          let uu____72454 =
                            let uu____72455 =
                              let uu____72456 =
                                let uu____72457 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72457
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72456
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72455
                             in
                          let uu____72459 =
                            let uu____72462 = mk_lam "_" body1  in
                            [uu____72462]  in
                          uu____72454 :: uu____72459  in
                        (uu____72449, uu____72451)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72442  in
                    FStar_All.pipe_left w uu____72441  in
                  mk_lam "args" body2
               in
            let uu____72467 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____72467 with
            | (bs,c) ->
                let uu____72500 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____72601 = FStar_Util.first_N n1 bs  in
                           match uu____72601 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____72679 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____72679
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____72696 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____72698 = FStar_Util.string_of_int n1
                                in
                             let uu____72700 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____72696 uu____72698 uu____72700
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____72500 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____72757 =
                       let uu____72778 =
                         FStar_Util.prefix_until
                           (fun uu____72820  ->
                              match uu____72820 with
                              | (b,uu____72829) ->
                                  let uu____72834 =
                                    let uu____72835 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____72835.FStar_Syntax_Syntax.n  in
                                  (match uu____72834 with
                                   | FStar_Syntax_Syntax.Tm_type uu____72839
                                       -> false
                                   | uu____72841 -> true)) bs1
                          in
                       match uu____72778 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____72757 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____73083 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____73083) type_vars
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
                                let uu____73183 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____73183
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____73204 =
                                      let uu____73207 =
                                        let uu____73210 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____73211 =
                                          let uu____73214 =
                                            let uu____73215 =
                                              let uu____73216 =
                                                let uu____73217 =
                                                  let uu____73229 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____73229,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____73217
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____73216
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____73215
                                             in
                                          [uu____73214; fv_lid_embedded; cb]
                                           in
                                        uu____73210 :: uu____73211  in
                                      res_embedding :: uu____73207  in
                                    FStar_List.append arg_unembeddings
                                      uu____73204
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
                                  let uu____73254 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____73254, arity, true)
                                else
                                  (let uu____73268 =
                                     let uu____73270 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____73270
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____73268
                                   then
                                     let h =
                                       let uu____73281 =
                                         let uu____73283 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____73283
                                          in
                                       str_to_top_name uu____73281  in
                                     let tac_fun =
                                       let uu____73292 =
                                         let uu____73293 =
                                           let uu____73300 =
                                             let uu____73301 =
                                               let uu____73303 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____73303
                                                in
                                             str_to_top_name uu____73301  in
                                           let uu____73311 =
                                             let uu____73314 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____73314]  in
                                           (uu____73300, uu____73311)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____73293
                                          in
                                       FStar_All.pipe_left w uu____73292  in
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
                                           let uu____73328 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____73328
                                       | uu____73332 ->
                                           let uu____73336 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____73336
                                        in
                                     let uu____73339 =
                                       let uu____73340 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____73340  in
                                     (uu____73339,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____73355 =
                                        let uu____73356 =
                                          let uu____73358 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____73358
                                           in
                                        NoTacticEmbedding uu____73356  in
                                      FStar_Exn.raise uu____73355))
                            | (b,uu____73370)::bs4 ->
                                let uu____73390 =
                                  let uu____73393 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____73393 :: accum_embeddings  in
                                aux loc uu____73390 bs4
                             in
                          (try
                             (fun uu___1304_73415  ->
                                match () with
                                | () ->
                                    let uu____73428 = aux Syntax_term [] bs2
                                       in
                                    (match uu____73428 with
                                     | (w1,a,b) ->
                                         let uu____73456 = aux NBE_t [] bs2
                                            in
                                         (match uu____73456 with
                                          | (w',uu____73478,uu____73479) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____73515 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____73515 msg);
                                FStar_Pervasives_Native.None))))
  