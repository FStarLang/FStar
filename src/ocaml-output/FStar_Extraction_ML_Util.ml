open Prims
let (codegen_fsharp : unit -> Prims.bool) =
  fun uu____67877  ->
    let uu____67878 = FStar_Options.codegen ()  in
    uu____67878 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____67947 ->
        FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____67977) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____67983) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_real uu____67988 ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: real/reify/reflect"
    | FStar_Const.Const_reflect uu____67992 ->
        failwith "Unhandled constant: real/reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try
        (fun uu___668_68006  -> match () with | () -> mlconst_of_const' c) ()
      with
      | uu___667_68009 ->
          let uu____68010 =
            let uu____68012 = FStar_Range.string_of_range p  in
            let uu____68014 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____68012 uu____68014
             in
          failwith uu____68010
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____68031 =
        let uu____68032 =
          let uu____68033 =
            let uu____68045 = FStar_Util.string_of_int i  in
            (uu____68045, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____68033  in
        FStar_All.pipe_right uu____68032
          (fun _68058  -> FStar_Extraction_ML_Syntax.MLE_Const _68058)
         in
      FStar_All.pipe_right uu____68031
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____68067 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _68068  -> FStar_Extraction_ML_Syntax.MLE_Const _68068)
         in
      FStar_All.pipe_right uu____68067
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____68069 =
      let uu____68076 =
        let uu____68079 =
          let uu____68080 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____68080 cstr  in
        let uu____68083 =
          let uu____68086 =
            let uu____68087 =
              let uu____68089 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____68089 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____68087 cint  in
          let uu____68092 =
            let uu____68095 =
              let uu____68096 =
                let uu____68098 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____68098 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____68096 cint  in
            let uu____68101 =
              let uu____68104 =
                let uu____68105 =
                  let uu____68107 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____68107 FStar_Range.line_of_pos
                   in
                FStar_All.pipe_right uu____68105 cint  in
              let uu____68110 =
                let uu____68113 =
                  let uu____68114 =
                    let uu____68116 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____68116 FStar_Range.col_of_pos
                     in
                  FStar_All.pipe_right uu____68114 cint  in
                [uu____68113]  in
              uu____68104 :: uu____68110  in
            uu____68095 :: uu____68101  in
          uu____68086 :: uu____68092  in
        uu____68079 :: uu____68083  in
      (mk_range_mle, uu____68076)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____68069
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____68133 ->
          let uu____68134 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____68134
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____68162 =
            FStar_Util.find_opt
              (fun uu____68178  ->
                 match uu____68178 with | (y,uu____68186) -> y = x) subst1
             in
          (match uu____68162 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____68210 =
            let uu____68217 = subst_aux subst1 t1  in
            let uu____68218 = subst_aux subst1 t2  in
            (uu____68217, f, uu____68218)  in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____68210
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____68225 =
            let uu____68232 = FStar_List.map (subst_aux subst1) args  in
            (uu____68232, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____68225
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____68240 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____68240
      | FStar_Extraction_ML_Syntax.MLTY_Top  -> t
      | FStar_Extraction_ML_Syntax.MLTY_Erased  -> t
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____68256  ->
    fun args  ->
      match uu____68256 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____68270 =
               let uu____68271 = FStar_List.zip formals args  in
               subst_aux uu____68271 t  in
             FStar_Pervasives_Native.Some uu____68270)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents * FStar_Extraction_ML_Syntax.mlty) ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____68303 = try_subst ts args  in
      match uu____68303 with
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
    fun uu___617_68320  ->
      match uu___617_68320 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____68329 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____68329 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____68335 = try_subst ts args  in
               (match uu____68335 with
                | FStar_Pervasives_Native.None  ->
                    let uu____68340 =
                      let uu____68342 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____68344 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____68346 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____68342 uu____68344 uu____68346
                       in
                    failwith uu____68340
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____68353 -> FStar_Pervasives_Native.None)
      | uu____68356 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____68370) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____68374 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___618_68386  ->
    match uu___618_68386 with
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
        | uu____68407 ->
            let uu____68412 =
              let uu____68414 = FStar_Range.string_of_range r  in
              let uu____68416 = eff_to_string f  in
              let uu____68418 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____68414
                uu____68416 uu____68418
               in
            failwith uu____68412
  
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
    (fun uu____68461  ->
       fun t  ->
         match uu____68461 with
         | (uu____68468,t0) ->
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
                | uu____68596 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____68633 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____68641 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____68641 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____68652;
                     FStar_Extraction_ML_Syntax.loc = uu____68653;_}
                   ->
                   let uu____68678 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____68678
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____68699 = type_leq unfold_ty t2 t2'  in
                        (if uu____68699
                         then
                           let body1 =
                             let uu____68713 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____68713
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____68721 =
                             let uu____68724 =
                               let uu____68725 =
                                 let uu____68730 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty
                                   uu____68730
                                  in
                               FStar_All.pipe_left uu____68725
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____68724  in
                           (true, uu____68721)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____68770 =
                           let uu____68778 =
                             let uu____68781 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _68784  ->
                                  FStar_Pervasives_Native.Some _68784)
                               uu____68781
                              in
                           type_leq_c unfold_ty uu____68778 t2 t2'  in
                         match uu____68770 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____68809 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____68809
                               | uu____68820 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____68832 ->
                   let uu____68835 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____68835
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____68881 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____68881
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____68906 = unfold_ty t  in
                 match uu____68906 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____68921 = unfold_ty t'  in
                     (match uu____68921 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____68946 =
                FStar_List.forall2 (type_leq unfold_ty) ts ts'  in
              if uu____68946
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____68973,uu____68974)
              ->
              let uu____68981 = unfold_ty t  in
              (match uu____68981 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____68996 -> (false, FStar_Pervasives_Native.None))
          | (uu____69003,FStar_Extraction_ML_Syntax.MLTY_Named uu____69004)
              ->
              let uu____69011 = unfold_ty t'  in
              (match uu____69011 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____69026 -> (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Erased
             ,FStar_Extraction_ML_Syntax.MLTY_Erased ) -> (true, e)
          | uu____69037 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____69052 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____69052 FStar_Pervasives_Native.fst

let rec (erase_effect_annotations :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____69083 =
          let uu____69090 = erase_effect_annotations t1  in
          let uu____69091 = erase_effect_annotations t2  in
          (uu____69090, FStar_Extraction_ML_Syntax.E_PURE, uu____69091)  in
        FStar_Extraction_ML_Syntax.MLTY_Fun uu____69083
    | uu____69092 -> t
  
let is_type_abstraction :
  'a 'b 'c . (('a,'b) FStar_Util.either * 'c) Prims.list -> Prims.bool =
  fun uu___619_69120  ->
    match uu___619_69120 with
    | (FStar_Util.Inl uu____69132,uu____69133)::uu____69134 -> true
    | uu____69158 -> false
  
let (is_xtuple :
  (Prims.string Prims.list * Prims.string) ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____69186  ->
    match uu____69186 with
    | (ns,n1) ->
        let uu____69208 =
          let uu____69210 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_datacon_string uu____69210  in
        if uu____69208
        then
          let uu____69220 =
            let uu____69222 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____69222  in
          FStar_Pervasives_Native.Some uu____69220
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____69241 = is_xtuple mlp  in
        (match uu____69241 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____69248 -> e)
    | uu____69252 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___620_69263  ->
    match uu___620_69263 with
    | f::uu____69270 ->
        let uu____69273 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____69273 with
         | (ns,uu____69284) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____69297 -> failwith "impos"
  
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
  fun uu____69363  ->
    match uu____69363 with
    | (ns,n1) ->
        let uu____69385 =
          let uu____69387 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____69387  in
        if uu____69385
        then
          let uu____69397 =
            let uu____69399 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____69399  in
          FStar_Pervasives_Native.Some uu____69397
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____69418 = is_xtuple_ty mlp  in
        (match uu____69418 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____69425 -> t)
    | uu____69429 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____69443 = codegen_fsharp ()  in
    if uu____69443
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list * Prims.string) -> Prims.string) =
  fun uu____69465  ->
    match uu____69465 with
    | (ns,n1) ->
        let uu____69485 = codegen_fsharp ()  in
        if uu____69485
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string)) =
  fun l  ->
    let uu____69513 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____69513, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____69547 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____69547
      then true
      else
        (let uu____69554 = unfold_ty t  in
         match uu____69554 with
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
            let uu____69584 =
              let uu____69591 = eraseTypeDeep unfold_ty tyd  in
              let uu____69595 = eraseTypeDeep unfold_ty tycd  in
              (uu____69591, etag, uu____69595)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____69584
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____69607 = erasableType unfold_ty t  in
          if uu____69607
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____69615 =
               let uu____69622 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____69622, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____69615)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____69633 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____69633
      | uu____69639 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____69650 =
    let uu____69655 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____69655  in
  FStar_All.pipe_left uu____69650
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
          let uu____69743 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____69743
  
let (mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string)) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____69759 = FStar_Range.file_of_range r  in (line, uu____69759)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69782,b) ->
        let uu____69784 = doms_and_cod b  in
        (match uu____69784 with | (ds,c) -> ((a :: ds), c))
    | uu____69805 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____69818 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____69818
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty))
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____69846,b) ->
        let uu____69848 = uncurry_mlty_fun b  in
        (match uu____69848 with | (args,res) -> ((a :: args), res))
    | uu____69869 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____69885 -> true
    | uu____69888 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____69899 -> uu____69899
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____69921 =
          let uu____69927 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____69927)  in
        FStar_Errors.log_issue r uu____69921
  
type emb_loc =
  | Syntax_term 
  | Refl_emb 
  | NBE_t 
  | NBERefl_emb 
let (uu___is_Syntax_term : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Syntax_term  -> true | uu____69940 -> false
  
let (uu___is_Refl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refl_emb  -> true | uu____69951 -> false
  
let (uu___is_NBE_t : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBE_t  -> true | uu____69962 -> false
  
let (uu___is_NBERefl_emb : emb_loc -> Prims.bool) =
  fun projectee  ->
    match projectee with | NBERefl_emb  -> true | uu____69973 -> false
  
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
              let uu____70044 =
                let uu____70045 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____70045  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70044
               in
            let lid_to_top_name l =
              let uu____70052 =
                let uu____70053 =
                  FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
                FStar_Extraction_ML_Syntax.MLE_Name uu____70053  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70052
               in
            let str_to_name s =
              let uu____70062 = FStar_Ident.lid_of_str s  in
              lid_to_name uu____70062  in
            let str_to_top_name s =
              let uu____70071 = FStar_Ident.lid_of_str s  in
              lid_to_top_name uu____70071  in
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
              let uu____70109 =
                let uu____70110 =
                  let uu____70117 = str_to_name "FStar_Ident.lid_of_str"  in
                  let uu____70119 =
                    let uu____70122 =
                      let uu____70123 =
                        let uu____70124 =
                          let uu____70125 = FStar_Ident.string_of_lid fv_lid1
                             in
                          FStar_Extraction_ML_Syntax.MLC_String uu____70125
                           in
                        FStar_Extraction_ML_Syntax.MLE_Const uu____70124  in
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____70123
                       in
                    [uu____70122]  in
                  (uu____70117, uu____70119)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70110  in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____70109
               in
            let emb_prefix uu___621_70140 =
              match uu___621_70140 with
              | Syntax_term  -> fstar_syn_emb_prefix
              | Refl_emb  -> fstar_refl_emb_prefix
              | NBE_t  -> fstar_tc_nbe_prefix
              | NBERefl_emb  -> fstar_refl_nbeemb_prefix  in
            let mk_tactic_interpretation l =
              match l with
              | Syntax_term  ->
                  "FStar_Tactics_InterpFuns.mk_tactic_interpretation_"
              | uu____70154 ->
                  "FStar_Tactics_InterpFuns.mk_nbe_tactic_interpretation_"
               in
            let mk_from_tactic l =
              match l with
              | Syntax_term  -> "FStar_Tactics_Native.from_tactic_"
              | uu____70165 -> "FStar_Tactics_Native.from_nbe_tactic_"  in
            let mk_basic_embedding l s = emb_prefix l (Prims.op_Hat "e_" s)
               in
            let mk_arrow_as_prim_step l arity =
              let uu____70194 =
                let uu____70196 = FStar_Util.string_of_int arity  in
                Prims.op_Hat "arrow_as_prim_step_" uu____70196  in
              emb_prefix l uu____70194  in
            let mk_any_embedding l s =
              let uu____70212 =
                let uu____70213 =
                  let uu____70220 = emb_prefix l "mk_any_emb"  in
                  let uu____70222 =
                    let uu____70225 = str_to_name s  in [uu____70225]  in
                  (uu____70220, uu____70222)  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70213  in
              FStar_All.pipe_left w uu____70212  in
            let mk_lam nm e =
              FStar_All.pipe_left w
                (FStar_Extraction_ML_Syntax.MLE_Fun
                   ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
               in
            let emb_arrow l e1 e2 =
              let uu____70275 =
                let uu____70276 =
                  let uu____70283 = emb_prefix l "e_arrow"  in
                  (uu____70283, [e1; e2])  in
                FStar_Extraction_ML_Syntax.MLE_App uu____70276  in
              FStar_All.pipe_left w uu____70275  in
            let known_type_constructors =
              let term_cs =
                let uu____70321 =
                  let uu____70336 =
                    let uu____70351 =
                      let uu____70366 =
                        let uu____70381 =
                          let uu____70396 =
                            let uu____70411 =
                              let uu____70426 =
                                let uu____70439 =
                                  let uu____70448 =
                                    FStar_Parser_Const.mk_tuple_lid
                                      (Prims.parse_int "2")
                                      FStar_Range.dummyRange
                                     in
                                  (uu____70448, (Prims.parse_int "2"),
                                    "tuple2")
                                   in
                                (uu____70439, Syntax_term)  in
                              let uu____70462 =
                                let uu____70477 =
                                  let uu____70490 =
                                    let uu____70499 =
                                      FStar_Reflection_Data.fstar_refl_types_lid
                                        "term"
                                       in
                                    (uu____70499, (Prims.parse_int "0"),
                                      "term")
                                     in
                                  (uu____70490, Refl_emb)  in
                                let uu____70513 =
                                  let uu____70528 =
                                    let uu____70541 =
                                      let uu____70550 =
                                        FStar_Reflection_Data.fstar_refl_types_lid
                                          "fv"
                                         in
                                      (uu____70550, (Prims.parse_int "0"),
                                        "fv")
                                       in
                                    (uu____70541, Refl_emb)  in
                                  let uu____70564 =
                                    let uu____70579 =
                                      let uu____70592 =
                                        let uu____70601 =
                                          FStar_Reflection_Data.fstar_refl_types_lid
                                            "binder"
                                           in
                                        (uu____70601, (Prims.parse_int "0"),
                                          "binder")
                                         in
                                      (uu____70592, Refl_emb)  in
                                    let uu____70615 =
                                      let uu____70630 =
                                        let uu____70643 =
                                          let uu____70652 =
                                            FStar_Reflection_Data.fstar_refl_syntax_lid
                                              "binders"
                                             in
                                          (uu____70652,
                                            (Prims.parse_int "0"), "binders")
                                           in
                                        (uu____70643, Refl_emb)  in
                                      let uu____70666 =
                                        let uu____70681 =
                                          let uu____70694 =
                                            let uu____70703 =
                                              FStar_Reflection_Data.fstar_refl_data_lid
                                                "exp"
                                               in
                                            (uu____70703,
                                              (Prims.parse_int "0"), "exp")
                                             in
                                          (uu____70694, Refl_emb)  in
                                        [uu____70681]  in
                                      uu____70630 :: uu____70666  in
                                    uu____70579 :: uu____70615  in
                                  uu____70528 :: uu____70564  in
                                uu____70477 :: uu____70513  in
                              uu____70426 :: uu____70462  in
                            ((FStar_Parser_Const.option_lid,
                               (Prims.parse_int "1"), "option"), Syntax_term)
                              :: uu____70411
                             in
                          ((FStar_Parser_Const.list_lid,
                             (Prims.parse_int "1"), "list"), Syntax_term)
                            :: uu____70396
                           in
                        ((FStar_Parser_Const.norm_step_lid,
                           (Prims.parse_int "0"), "norm_step"), Syntax_term)
                          :: uu____70381
                         in
                      ((FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                         "string"), Syntax_term)
                        :: uu____70366
                       in
                    ((FStar_Parser_Const.unit_lid, (Prims.parse_int "0"),
                       "unit"), Syntax_term)
                      :: uu____70351
                     in
                  ((FStar_Parser_Const.bool_lid, (Prims.parse_int "0"),
                     "bool"), Syntax_term)
                    :: uu____70336
                   in
                ((FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int"),
                  Syntax_term) :: uu____70321
                 in
              let nbe_cs =
                FStar_List.map
                  (fun uu___622_71010  ->
                     match uu___622_71010 with
                     | (x,Syntax_term ) -> (x, NBE_t)
                     | (x,Refl_emb ) -> (x, NBERefl_emb)
                     | uu____71085 -> failwith "Impossible") term_cs
                 in
              fun uu___623_71111  ->
                match uu___623_71111 with
                | Syntax_term  -> term_cs
                | Refl_emb  -> term_cs
                | uu____71126 -> nbe_cs
               in
            let is_known_type_constructor l fv1 n1 =
              FStar_Util.for_some
                (fun uu____71163  ->
                   match uu____71163 with
                   | ((x,args,uu____71179),uu____71180) ->
                       (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
                (known_type_constructors l)
               in
            let find_env_entry bv uu____71210 =
              match uu____71210 with
              | (bv',uu____71218) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
            let rec mk_embedding l env t2 =
              let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
              let uu____71252 =
                let uu____71253 = FStar_Syntax_Subst.compress t3  in
                uu____71253.FStar_Syntax_Syntax.n  in
              match uu____71252 with
              | FStar_Syntax_Syntax.Tm_name bv when
                  FStar_Util.for_some (find_env_entry bv) env ->
                  let uu____71262 =
                    let uu____71264 =
                      let uu____71270 =
                        FStar_Util.find_opt (find_env_entry bv) env  in
                      FStar_Util.must uu____71270  in
                    FStar_Pervasives_Native.snd uu____71264  in
                  FStar_All.pipe_left (mk_any_embedding l) uu____71262
              | FStar_Syntax_Syntax.Tm_refine (x,uu____71291) ->
                  mk_embedding l env x.FStar_Syntax_Syntax.sort
              | FStar_Syntax_Syntax.Tm_ascribed (t4,uu____71297,uu____71298)
                  -> mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_arrow (b::[],c) when
                  FStar_Syntax_Util.is_pure_comp c ->
                  let uu____71371 = FStar_Syntax_Subst.open_comp [b] c  in
                  (match uu____71371 with
                   | (bs,c1) ->
                       let t0 =
                         let uu____71393 =
                           let uu____71394 = FStar_List.hd bs  in
                           FStar_Pervasives_Native.fst uu____71394  in
                         uu____71393.FStar_Syntax_Syntax.sort  in
                       let t11 = FStar_Syntax_Util.comp_result c1  in
                       let uu____71412 = mk_embedding l env t0  in
                       let uu____71413 = mk_embedding l env t11  in
                       emb_arrow l uu____71412 uu____71413)
              | FStar_Syntax_Syntax.Tm_arrow (b::more::bs,c) ->
                  let tail1 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow ((more :: bs), c))
                      FStar_Pervasives_Native.None t3.FStar_Syntax_Syntax.pos
                     in
                  let t4 =
                    let uu____71484 =
                      let uu____71491 =
                        let uu____71492 =
                          let uu____71507 =
                            FStar_Syntax_Syntax.mk_Total tail1  in
                          ([b], uu____71507)  in
                        FStar_Syntax_Syntax.Tm_arrow uu____71492  in
                      FStar_Syntax_Syntax.mk uu____71491  in
                    uu____71484 FStar_Pervasives_Native.None
                      t3.FStar_Syntax_Syntax.pos
                     in
                  mk_embedding l env t4
              | FStar_Syntax_Syntax.Tm_fvar uu____71535 ->
                  let uu____71536 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71536 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71588 =
                         let uu____71589 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71589.FStar_Syntax_Syntax.n  in
                       (match uu____71588 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71619  ->
                                      match uu____71619 with
                                      | (t4,uu____71627) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71634 =
                              let uu____71647 =
                                FStar_Util.find_opt
                                  (fun uu____71679  ->
                                     match uu____71679 with
                                     | ((x,uu____71694,uu____71695),uu____71696)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71647
                                FStar_Util.must
                               in
                            (match uu____71634 with
                             | ((uu____71747,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _71764 when
                                      _71764 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____71769 ->
                            let uu____71770 =
                              let uu____71771 =
                                let uu____71773 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____71773
                                 in
                              NoTacticEmbedding uu____71771  in
                            FStar_Exn.raise uu____71770))
              | FStar_Syntax_Syntax.Tm_uinst uu____71776 ->
                  let uu____71783 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____71783 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____71835 =
                         let uu____71836 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____71836.FStar_Syntax_Syntax.n  in
                       (match uu____71835 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____71866  ->
                                      match uu____71866 with
                                      | (t4,uu____71874) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____71881 =
                              let uu____71894 =
                                FStar_Util.find_opt
                                  (fun uu____71926  ->
                                     match uu____71926 with
                                     | ((x,uu____71941,uu____71942),uu____71943)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____71894
                                FStar_Util.must
                               in
                            (match uu____71881 with
                             | ((uu____71994,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72011 when
                                      _72011 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72016 ->
                            let uu____72017 =
                              let uu____72018 =
                                let uu____72020 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72020
                                 in
                              NoTacticEmbedding uu____72018  in
                            FStar_Exn.raise uu____72017))
              | FStar_Syntax_Syntax.Tm_app uu____72023 ->
                  let uu____72040 = FStar_Syntax_Util.head_and_args t3  in
                  (match uu____72040 with
                   | (head1,args) ->
                       let n_args = FStar_List.length args  in
                       let uu____72092 =
                         let uu____72093 = FStar_Syntax_Util.un_uinst head1
                            in
                         uu____72093.FStar_Syntax_Syntax.n  in
                       (match uu____72092 with
                        | FStar_Syntax_Syntax.Tm_fvar fv1 when
                            is_known_type_constructor l fv1 n_args ->
                            let arg_embeddings =
                              FStar_All.pipe_right args
                                (FStar_List.map
                                   (fun uu____72123  ->
                                      match uu____72123 with
                                      | (t4,uu____72131) ->
                                          mk_embedding l env t4))
                               in
                            let nm =
                              (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                               in
                            let uu____72138 =
                              let uu____72151 =
                                FStar_Util.find_opt
                                  (fun uu____72183  ->
                                     match uu____72183 with
                                     | ((x,uu____72198,uu____72199),uu____72200)
                                         ->
                                         FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                  (known_type_constructors l)
                                 in
                              FStar_All.pipe_right uu____72151
                                FStar_Util.must
                               in
                            (match uu____72138 with
                             | ((uu____72251,t_arity,_trepr_head),loc_embedding)
                                 ->
                                 let head2 =
                                   mk_basic_embedding loc_embedding nm  in
                                 (match t_arity with
                                  | _72268 when
                                      _72268 = (Prims.parse_int "0") -> head2
                                  | n1 ->
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (head2, arg_embeddings))))
                        | uu____72273 ->
                            let uu____72274 =
                              let uu____72275 =
                                let uu____72277 =
                                  FStar_Syntax_Print.term_to_string t3  in
                                Prims.op_Hat
                                  "Embedding not defined for type "
                                  uu____72277
                                 in
                              NoTacticEmbedding uu____72275  in
                            FStar_Exn.raise uu____72274))
              | uu____72280 ->
                  let uu____72281 =
                    let uu____72282 =
                      let uu____72284 = FStar_Syntax_Print.term_to_string t3
                         in
                      Prims.op_Hat "Embedding not defined for type "
                        uu____72284
                       in
                    NoTacticEmbedding uu____72282  in
                  FStar_Exn.raise uu____72281
               in
            let abstract_tvars tvar_names body =
              match tvar_names with
              | [] ->
                  let body1 =
                    let uu____72306 =
                      let uu____72307 =
                        let uu____72314 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72316 =
                          let uu____72319 =
                            let uu____72320 =
                              let uu____72321 =
                                let uu____72322 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72322
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72321
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72320
                             in
                          let uu____72324 =
                            let uu____72327 =
                              let uu____72328 =
                                let uu____72329 =
                                  let uu____72330 =
                                    let uu____72337 =
                                      let uu____72340 = str_to_name "args"
                                         in
                                      [uu____72340]  in
                                    (body, uu____72337)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____72330
                                   in
                                FStar_All.pipe_left w uu____72329  in
                              mk_lam "_" uu____72328  in
                            [uu____72327]  in
                          uu____72319 :: uu____72324  in
                        (uu____72314, uu____72316)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72307  in
                    FStar_All.pipe_left w uu____72306  in
                  mk_lam "args" body1
              | uu____72348 ->
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
                    let uu____72397 =
                      let uu____72398 =
                        let uu____72399 =
                          let uu____72406 =
                            let uu____72409 = str_to_name "args"  in
                            [uu____72409]  in
                          (body, uu____72406)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72399  in
                      FStar_All.pipe_left w uu____72398  in
                    (pattern, FStar_Pervasives_Native.None, uu____72397)  in
                  let default_branch =
                    let uu____72424 =
                      let uu____72425 =
                        let uu____72426 =
                          let uu____72433 = str_to_name "failwith"  in
                          let uu____72435 =
                            let uu____72438 =
                              let uu____72439 =
                                mlexpr_of_const FStar_Range.dummyRange
                                  (FStar_Const.Const_string
                                     ("arity mismatch",
                                       FStar_Range.dummyRange))
                                 in
                              FStar_All.pipe_left w uu____72439  in
                            [uu____72438]  in
                          (uu____72433, uu____72435)  in
                        FStar_Extraction_ML_Syntax.MLE_App uu____72426  in
                      FStar_All.pipe_left w uu____72425  in
                    (FStar_Extraction_ML_Syntax.MLP_Wild,
                      FStar_Pervasives_Native.None, uu____72424)
                     in
                  let body1 =
                    let uu____72447 =
                      let uu____72448 =
                        let uu____72463 = str_to_name "args"  in
                        (uu____72463, [branch1; default_branch])  in
                      FStar_Extraction_ML_Syntax.MLE_Match uu____72448  in
                    FStar_All.pipe_left w uu____72447  in
                  let body2 =
                    let uu____72500 =
                      let uu____72501 =
                        let uu____72508 =
                          str_to_name "FStar_Syntax_Embeddings.debug_wrap"
                           in
                        let uu____72510 =
                          let uu____72513 =
                            let uu____72514 =
                              let uu____72515 =
                                let uu____72516 =
                                  FStar_Ident.string_of_lid fv_lid1  in
                                FStar_Extraction_ML_Syntax.MLC_String
                                  uu____72516
                                 in
                              FStar_Extraction_ML_Syntax.MLE_Const
                                uu____72515
                               in
                            FStar_All.pipe_left
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                              uu____72514
                             in
                          let uu____72518 =
                            let uu____72521 = mk_lam "_" body1  in
                            [uu____72521]  in
                          uu____72513 :: uu____72518  in
                        (uu____72508, uu____72510)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____72501  in
                    FStar_All.pipe_left w uu____72500  in
                  mk_lam "args" body2
               in
            let uu____72526 = FStar_Syntax_Util.arrow_formals_comp t1  in
            match uu____72526 with
            | (bs,c) ->
                let uu____72559 =
                  match arity_opt with
                  | FStar_Pervasives_Native.None  -> (bs, c)
                  | FStar_Pervasives_Native.Some n1 ->
                      let n_bs = FStar_List.length bs  in
                      if n1 = n_bs
                      then (bs, c)
                      else
                        if n1 < n_bs
                        then
                          (let uu____72660 = FStar_Util.first_N n1 bs  in
                           match uu____72660 with
                           | (bs1,rest) ->
                               let c1 =
                                 let uu____72738 =
                                   FStar_Syntax_Util.arrow rest c  in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Syntax.mk_Total uu____72738
                                  in
                               (bs1, c1))
                        else
                          (let msg =
                             let uu____72755 =
                               FStar_Ident.string_of_lid fv_lid1  in
                             let uu____72757 = FStar_Util.string_of_int n1
                                in
                             let uu____72759 = FStar_Util.string_of_int n_bs
                                in
                             FStar_Util.format3
                               "Embedding not defined for %s; expected arity at least %s; got %s"
                               uu____72755 uu____72757 uu____72759
                              in
                           FStar_Exn.raise (NoTacticEmbedding msg))
                   in
                (match uu____72559 with
                 | (bs1,c1) ->
                     let result_typ = FStar_Syntax_Util.comp_result c1  in
                     let arity = FStar_List.length bs1  in
                     let uu____72816 =
                       let uu____72837 =
                         FStar_Util.prefix_until
                           (fun uu____72879  ->
                              match uu____72879 with
                              | (b,uu____72888) ->
                                  let uu____72893 =
                                    let uu____72894 =
                                      FStar_Syntax_Subst.compress
                                        b.FStar_Syntax_Syntax.sort
                                       in
                                    uu____72894.FStar_Syntax_Syntax.n  in
                                  (match uu____72893 with
                                   | FStar_Syntax_Syntax.Tm_type uu____72898
                                       -> false
                                   | uu____72900 -> true)) bs1
                          in
                       match uu____72837 with
                       | FStar_Pervasives_Native.None  -> (bs1, [])
                       | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                           (tvars, (x :: rest))
                        in
                     (match uu____72816 with
                      | (type_vars,bs2) ->
                          let tvar_arity = FStar_List.length type_vars  in
                          let non_tvar_arity = FStar_List.length bs2  in
                          let tvar_names =
                            FStar_List.mapi
                              (fun i  ->
                                 fun tv  ->
                                   let uu____73142 =
                                     FStar_Util.string_of_int i  in
                                   Prims.op_Hat "tv_" uu____73142) type_vars
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
                                let uu____73242 =
                                  FStar_Syntax_Util.is_pure_comp c1  in
                                if uu____73242
                                then
                                  let cb = str_to_name "cb"  in
                                  let embed_fun_N =
                                    mk_arrow_as_prim_step loc non_tvar_arity
                                     in
                                  let args =
                                    let uu____73263 =
                                      let uu____73266 =
                                        let uu____73269 =
                                          lid_to_top_name fv_lid2  in
                                        let uu____73270 =
                                          let uu____73273 =
                                            let uu____73274 =
                                              let uu____73275 =
                                                let uu____73276 =
                                                  let uu____73288 =
                                                    FStar_Util.string_of_int
                                                      tvar_arity
                                                     in
                                                  (uu____73288,
                                                    FStar_Pervasives_Native.None)
                                                   in
                                                FStar_Extraction_ML_Syntax.MLC_Int
                                                  uu____73276
                                                 in
                                              FStar_Extraction_ML_Syntax.MLE_Const
                                                uu____73275
                                               in
                                            FStar_All.pipe_left
                                              (FStar_Extraction_ML_Syntax.with_ty
                                                 FStar_Extraction_ML_Syntax.MLTY_Top)
                                              uu____73274
                                             in
                                          [uu____73273; fv_lid_embedded; cb]
                                           in
                                        uu____73269 :: uu____73270  in
                                      res_embedding :: uu____73266  in
                                    FStar_List.append arg_unembeddings
                                      uu____73263
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
                                  let uu____73313 =
                                    if loc = NBE_t
                                    then cb_tabs
                                    else mk_lam "_psc" cb_tabs  in
                                  (uu____73313, arity, true)
                                else
                                  (let uu____73327 =
                                     let uu____73329 =
                                       FStar_TypeChecker_Env.norm_eff_name
                                         tcenv
                                         (FStar_Syntax_Util.comp_effect_name
                                            c1)
                                        in
                                     FStar_Ident.lid_equals uu____73329
                                       FStar_Parser_Const.effect_TAC_lid
                                      in
                                   if uu____73327
                                   then
                                     let h =
                                       let uu____73340 =
                                         let uu____73342 =
                                           FStar_Util.string_of_int
                                             non_tvar_arity
                                            in
                                         Prims.op_Hat
                                           (mk_tactic_interpretation loc)
                                           uu____73342
                                          in
                                       str_to_top_name uu____73340  in
                                     let tac_fun =
                                       let uu____73351 =
                                         let uu____73352 =
                                           let uu____73359 =
                                             let uu____73360 =
                                               let uu____73362 =
                                                 FStar_Util.string_of_int
                                                   non_tvar_arity
                                                  in
                                               Prims.op_Hat
                                                 (mk_from_tactic loc)
                                                 uu____73362
                                                in
                                             str_to_top_name uu____73360  in
                                           let uu____73370 =
                                             let uu____73373 =
                                               lid_to_top_name fv_lid2  in
                                             [uu____73373]  in
                                           (uu____73359, uu____73370)  in
                                         FStar_Extraction_ML_Syntax.MLE_App
                                           uu____73352
                                          in
                                       FStar_All.pipe_left w uu____73351  in
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
                                           let uu____73387 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h,
                                                    (FStar_List.append args
                                                       [all_args])))
                                              in
                                           mk_lam "args" uu____73387
                                       | uu____73391 ->
                                           let uu____73395 =
                                             FStar_All.pipe_left w
                                               (FStar_Extraction_ML_Syntax.MLE_App
                                                  (h, args))
                                              in
                                           abstract_tvars tvar_names
                                             uu____73395
                                        in
                                     let uu____73398 =
                                       let uu____73399 = mk_lam "ncb" tabs
                                          in
                                       mk_lam "psc" uu____73399  in
                                     (uu____73398,
                                       (arity + (Prims.parse_int "1")),
                                       false)
                                   else
                                     (let uu____73414 =
                                        let uu____73415 =
                                          let uu____73417 =
                                            FStar_Syntax_Print.term_to_string
                                              t1
                                             in
                                          Prims.op_Hat
                                            "Plugins not defined for type "
                                            uu____73417
                                           in
                                        NoTacticEmbedding uu____73415  in
                                      FStar_Exn.raise uu____73414))
                            | (b,uu____73429)::bs4 ->
                                let uu____73449 =
                                  let uu____73452 =
                                    mk_embedding loc tvar_context
                                      b.FStar_Syntax_Syntax.sort
                                     in
                                  uu____73452 :: accum_embeddings  in
                                aux loc uu____73449 bs4
                             in
                          (try
                             (fun uu___1304_73474  ->
                                match () with
                                | () ->
                                    let uu____73487 = aux Syntax_term [] bs2
                                       in
                                    (match uu____73487 with
                                     | (w1,a,b) ->
                                         let uu____73515 = aux NBE_t [] bs2
                                            in
                                         (match uu____73515 with
                                          | (w',uu____73537,uu____73538) ->
                                              FStar_Pervasives_Native.Some
                                                (w1, w', a, b)))) ()
                           with
                           | NoTacticEmbedding msg ->
                               ((let uu____73574 =
                                   FStar_Syntax_Print.fv_to_string fv  in
                                 not_implemented_warning
                                   t1.FStar_Syntax_Syntax.pos uu____73574 msg);
                                FStar_Pervasives_Native.None))))
  