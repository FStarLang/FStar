open Prims
let (codegen_fsharp : Prims.unit -> Prims.bool) =
  fun uu____3  ->
    let uu____4 = FStar_Options.codegen ()  in
    uu____4 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)
  
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
    | FStar_Const.Const_range uu____49 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____74) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____80) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____81 ->
        failwith "Unhandled constant: reify/reflect"
  
let (mlconst_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant)
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const' c
      with
      | uu____94 ->
          let uu____95 =
            let uu____96 = FStar_Range.string_of_range p  in
            let uu____97 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____96 uu____97
             in
          failwith uu____95
  
let (mlexpr_of_range :
  FStar_Range.range -> FStar_Extraction_ML_Syntax.mlexpr') =
  fun r  ->
    let cint i =
      let uu____105 =
        let uu____106 =
          let uu____107 =
            let uu____118 = FStar_Util.string_of_int i  in
            (uu____118, FStar_Pervasives_Native.None)  in
          FStar_Extraction_ML_Syntax.MLC_Int uu____107  in
        FStar_All.pipe_right uu____106
          (fun _0_41  -> FStar_Extraction_ML_Syntax.MLE_Const _0_41)
         in
      FStar_All.pipe_right uu____105
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_int_ty)
       in
    let cstr s =
      let uu____133 =
        FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
          (fun _0_42  -> FStar_Extraction_ML_Syntax.MLE_Const _0_42)
         in
      FStar_All.pipe_right uu____133
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_string_ty)
       in
    let uu____134 =
      let uu____141 =
        let uu____144 =
          let uu____145 = FStar_Range.file_of_range r  in
          FStar_All.pipe_right uu____145 cstr  in
        let uu____146 =
          let uu____149 =
            let uu____150 =
              let uu____151 = FStar_Range.start_of_range r  in
              FStar_All.pipe_right uu____151 FStar_Range.line_of_pos  in
            FStar_All.pipe_right uu____150 cint  in
          let uu____152 =
            let uu____155 =
              let uu____156 =
                let uu____157 = FStar_Range.start_of_range r  in
                FStar_All.pipe_right uu____157 FStar_Range.col_of_pos  in
              FStar_All.pipe_right uu____156 cint  in
            let uu____158 =
              let uu____161 =
                let uu____162 =
                  let uu____163 = FStar_Range.end_of_range r  in
                  FStar_All.pipe_right uu____163 FStar_Range.line_of_pos  in
                FStar_All.pipe_right uu____162 cint  in
              let uu____164 =
                let uu____167 =
                  let uu____168 =
                    let uu____169 = FStar_Range.end_of_range r  in
                    FStar_All.pipe_right uu____169 FStar_Range.col_of_pos  in
                  FStar_All.pipe_right uu____168 cint  in
                [uu____167]  in
              uu____161 :: uu____164  in
            uu____155 :: uu____158  in
          uu____149 :: uu____152  in
        uu____144 :: uu____146  in
      (mk_range_mle, uu____141)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____134
  
let (mlexpr_of_const :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r -> mlexpr_of_range r
      | uu____179 ->
          let uu____180 = mlconst_of_const p c  in
          FStar_Extraction_ML_Syntax.MLE_Const uu____180
  
let rec (subst_aux :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____200 =
            FStar_Util.find_opt
              (fun uu____214  ->
                 match uu____214 with | (y,uu____220) -> y = x) subst1
             in
          (match uu____200 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____237 =
            let uu____244 = subst_aux subst1 t1  in
            let uu____245 = subst_aux subst1 t2  in (uu____244, f, uu____245)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____237
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____252 =
            let uu____259 = FStar_List.map (subst_aux subst1) args  in
            (uu____259, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____252
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____267 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____267
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
  
let (try_subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun uu____278  ->
    fun args  ->
      match uu____278 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____289 =
               let uu____290 = FStar_List.zip formals args  in
               subst_aux uu____290 t  in
             FStar_Pervasives_Native.Some uu____289)
  
let (subst :
  (FStar_Extraction_ML_Syntax.mlidents,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun ts  ->
    fun args  ->
      let uu____315 = try_subst ts args  in
      match uu____315 with
      | FStar_Pervasives_Native.None  ->
          failwith
            "Substitution must be fully applied (see GitHub issue #490)"
      | FStar_Pervasives_Native.Some t -> t
  
let (udelta_unfold :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun uu___61_326  ->
      match uu___61_326 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____335 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____335 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____341 = try_subst ts args  in
               (match uu____341 with
                | FStar_Pervasives_Native.None  ->
                    let uu____346 =
                      let uu____347 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1  in
                      let uu____348 =
                        FStar_Util.string_of_int (FStar_List.length args)  in
                      let uu____349 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts))
                         in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____347 uu____348 uu____349
                       in
                    failwith uu____346
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____353 -> FStar_Pervasives_Native.None)
      | uu____356 -> FStar_Pervasives_Native.None
  
let (eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool)
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____363) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____364 -> false
  
let (eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string) =
  fun uu___62_371  ->
    match uu___62_371 with
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
        | uu____381 ->
            let uu____386 =
              let uu____387 = FStar_Range.string_of_range r  in
              let uu____388 = eff_to_string f  in
              let uu____389 = eff_to_string f'  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____387
                uu____388 uu____389
               in
            failwith uu____386
  
let (join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag)
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
  
let (mk_ty_fun :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  FStar_List.fold_right
    (fun uu____418  ->
       fun t  ->
         match uu____418 with
         | (uu____424,t0) ->
             FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
  
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option[@@deriving
                                                                    show]
let rec (type_leq_c :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2)
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
                | uu____511 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____543 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____550 =
                      mk_ty_fun xs body.FStar_Extraction_ML_Syntax.mlty  in
                    FStar_Extraction_ML_Syntax.with_ty uu____550 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____560;
                     FStar_Extraction_ML_Syntax.loc = uu____561;_}
                   ->
                   let uu____582 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____582
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____598 = type_leq unfold_ty t2 t2'  in
                        (if uu____598
                         then
                           let body1 =
                             let uu____609 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____609
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____614 =
                             let uu____617 =
                               let uu____618 =
                                 let uu____621 =
                                   mk_ty_fun [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____621
                                  in
                               FStar_All.pipe_left uu____618
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____617  in
                           (true, uu____614)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____650 =
                           let uu____657 =
                             let uu____660 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_43  ->
                                  FStar_Pervasives_Native.Some _0_43)
                               uu____660
                              in
                           type_leq_c unfold_ty uu____657 t2 t2'  in
                         match uu____650 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____684 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____684
                               | uu____693 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____701 ->
                   let uu____704 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____704
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____740 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____740
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____756 = unfold_ty t  in
                 match uu____756 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____770 = unfold_ty t'  in
                     (match uu____770 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____792 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____792
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____809,uu____810) ->
              let uu____817 = unfold_ty t  in
              (match uu____817 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____831 -> (false, FStar_Pervasives_Native.None))
          | (uu____836,FStar_Extraction_ML_Syntax.MLTY_Named uu____837) ->
              let uu____844 = unfold_ty t'  in
              (match uu____844 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____858 -> (false, FStar_Pervasives_Native.None))
          | uu____863 -> (false, FStar_Pervasives_Native.None)

and (type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____874 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____874 FStar_Pervasives_Native.fst

let is_type_abstraction :
  'a 'b 'c .
    (('a,'b) FStar_Util.either,'c) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.bool
  =
  fun uu___63_912  ->
    match uu___63_912 with
    | (FStar_Util.Inl uu____923,uu____924)::uu____925 -> true
    | uu____948 -> false
  
let (is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____969  ->
    match uu____969 with
    | (ns,n1) ->
        let uu____984 =
          let uu____985 = FStar_Util.concat_l "." (FStar_List.append ns [n1])
             in
          FStar_Parser_Const.is_tuple_datacon_string uu____985  in
        if uu____984
        then
          let uu____988 =
            let uu____989 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____989  in
          FStar_Pervasives_Native.Some uu____988
        else FStar_Pervasives_Native.None
  
let (resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1000 = is_xtuple mlp  in
        (match uu____1000 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1004 -> e)
    | uu____1007 -> e
  
let (record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list) =
  fun uu___64_1014  ->
    match uu___64_1014 with
    | f::uu____1020 ->
        let uu____1023 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____1023 with
         | (ns,uu____1033) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id1  -> id1.FStar_Ident.idText)))
    | uu____1044 -> failwith "impos"
  
let record_fields :
  'a .
    FStar_Ident.lident Prims.list ->
      'a Prims.list ->
        (Prims.string,'a) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2
        (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e))
        fs vs
  
let (is_xtuple_ty :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option)
  =
  fun uu____1093  ->
    match uu____1093 with
    | (ns,n1) ->
        let uu____1108 =
          let uu____1109 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1])  in
          FStar_Parser_Const.is_tuple_constructor_string uu____1109  in
        if uu____1108
        then
          let uu____1112 =
            let uu____1113 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____1113  in
          FStar_Pervasives_Native.Some uu____1112
        else FStar_Pervasives_Native.None
  
let (resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty) =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1124 = is_xtuple_ty mlp  in
        (match uu____1124 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1128 -> t)
    | uu____1131 -> t
  
let (flatten_ns : Prims.string Prims.list -> Prims.string) =
  fun ns  ->
    let uu____1139 = codegen_fsharp ()  in
    if uu____1139
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let (flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string)
  =
  fun uu____1149  ->
    match uu____1149 with
    | (ns,n1) ->
        let uu____1162 = codegen_fsharp ()  in
        if uu____1162
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let (mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    let uu____1173 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____1173, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec (erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun unfold_ty  ->
    fun t  ->
      let uu____1193 = FStar_Extraction_ML_UEnv.erasableTypeNoDelta t  in
      if uu____1193
      then true
      else
        (let uu____1195 = unfold_ty t  in
         match uu____1195 with
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
            let uu____1215 =
              let uu____1222 = eraseTypeDeep unfold_ty tyd  in
              let uu____1226 = eraseTypeDeep unfold_ty tycd  in
              (uu____1222, etag, uu____1226)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1215
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1237 = erasableType unfold_ty t  in
          if uu____1237
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1242 =
               let uu____1249 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____1249, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1242)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1260 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1260
      | uu____1266 -> t
  
let (prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr) =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let (prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr) =
  let uu____1269 =
    let uu____1272 =
      mk_ty_fun
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____1272  in
  FStar_All.pipe_left uu____1269
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
          let uu____1337 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____1337
  
let (mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____1347 = FStar_Range.file_of_range r  in (line, uu____1347)
  
let rec (doms_and_cod :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1364,b) ->
        let uu____1366 = doms_and_cod b  in
        (match uu____1366 with | (ds,c) -> ((a :: ds), c))
    | uu____1387 -> ([], t)
  
let (argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list)
  =
  fun t  ->
    let uu____1397 = doms_and_cod t  in
    FStar_Pervasives_Native.fst uu____1397
  
let rec (uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1422,b) ->
        let uu____1424 = uncurry_mlty_fun b  in
        (match uu____1424 with | (args,res) -> ((a :: args), res))
    | uu____1445 -> ([], t)
  
exception NoTacticEmbedding of Prims.string 
let (uu___is_NoTacticEmbedding : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | NoTacticEmbedding uu____1454 -> true
    | uu____1455 -> false
  
let (__proj__NoTacticEmbedding__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | NoTacticEmbedding uu____1462 -> uu____1462
  
let (not_implemented_warning :
  FStar_Range.range -> Prims.string -> Prims.string -> Prims.unit) =
  fun r  ->
    fun t  ->
      fun msg  ->
        let uu____1472 =
          let uu____1477 =
            FStar_Util.format2
              "Plugin %s will not run natively because %s.\n" t msg
             in
          (FStar_Errors.Warning_CallNotImplementedAsWarning, uu____1477)  in
        FStar_Errors.log_issue r uu____1472
  
type emb_loc =
  | S 
  | R [@@deriving show]
let (uu___is_S : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | S  -> true | uu____1481 -> false 
let (uu___is_R : emb_loc -> Prims.bool) =
  fun projectee  -> match projectee with | R  -> true | uu____1485 -> false 
let (interpret_plugin_as_term_fun :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mlexpr' ->
          (FStar_Extraction_ML_Syntax.mlexpr,Prims.int,Prims.bool)
            FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun tcenv  ->
    fun fv  ->
      fun t  ->
        fun ml_fv  ->
          let t1 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Normalize.EraseUniverses;
              FStar_TypeChecker_Normalize.AllowUnboundUniverses;
              FStar_TypeChecker_Normalize.UnfoldUntil
                FStar_Syntax_Syntax.Delta_constant] tcenv t
             in
          let w =
            FStar_Extraction_ML_Syntax.with_ty
              FStar_Extraction_ML_Syntax.MLTY_Top
             in
          let lid_to_name l =
            let uu____1514 =
              let uu____1515 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1515  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1514
             in
          let lid_to_top_name l =
            let uu____1520 =
              let uu____1521 = FStar_Extraction_ML_Syntax.mlpath_of_lident l
                 in
              FStar_Extraction_ML_Syntax.MLE_Name uu____1521  in
            FStar_All.pipe_left
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.MLTY_Top) uu____1520
             in
          let str_to_name s =
            let uu____1526 = FStar_Ident.lid_of_str s  in
            lid_to_name uu____1526  in
          let str_to_top_name s =
            let uu____1531 = FStar_Ident.lid_of_str s  in
            lid_to_top_name uu____1531  in
          let fstar_syn_emb_prefix s =
            str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)  in
          let fstar_refl_emb_prefix s =
            str_to_name (Prims.strcat "FStar_Reflection_Embeddings." s)  in
          let mk_basic_embedding l s =
            let emb_prefix =
              match l with
              | S  -> fstar_syn_emb_prefix
              | R  -> fstar_refl_emb_prefix  in
            emb_prefix (Prims.strcat "e_" s)  in
          let mk_arrow_embedding arity =
            let uu____1556 =
              let uu____1557 = FStar_Util.string_of_int arity  in
              Prims.strcat "embed_arrow_" uu____1557  in
            fstar_syn_emb_prefix uu____1556  in
          let mk_any_embedding s =
            let uu____1562 =
              let uu____1563 =
                let uu____1570 = fstar_syn_emb_prefix "mk_any_emb"  in
                let uu____1571 =
                  let uu____1574 = str_to_name s  in [uu____1574]  in
                (uu____1570, uu____1571)  in
              FStar_Extraction_ML_Syntax.MLE_App uu____1563  in
            FStar_All.pipe_left w uu____1562  in
          let mk_lam nm e =
            FStar_All.pipe_left w
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([(nm, FStar_Extraction_ML_Syntax.MLTY_Top)], e))
             in
          let known_type_constructors =
            let uu____1609 =
              let uu____1620 =
                let uu____1631 =
                  let uu____1642 =
                    let uu____1653 =
                      let uu____1662 =
                        FStar_Reflection_Data.fstar_refl_types_lid "term"  in
                      (uu____1662, (Prims.parse_int "0"), "term", R)  in
                    let uu____1663 =
                      let uu____1674 =
                        let uu____1683 =
                          FStar_Reflection_Data.fstar_refl_types_lid "fv"  in
                        (uu____1683, (Prims.parse_int "0"), "fv", R)  in
                      let uu____1684 =
                        let uu____1695 =
                          let uu____1704 =
                            FStar_Reflection_Data.fstar_refl_types_lid
                              "binder"
                             in
                          (uu____1704, (Prims.parse_int "0"), "binder", R)
                           in
                        let uu____1705 =
                          let uu____1716 =
                            let uu____1725 =
                              FStar_Reflection_Data.fstar_refl_syntax_lid
                                "binders"
                               in
                            (uu____1725, (Prims.parse_int "0"), "binders", R)
                             in
                          let uu____1726 =
                            let uu____1737 =
                              let uu____1748 =
                                let uu____1759 =
                                  let uu____1770 =
                                    let uu____1779 =
                                      FStar_Parser_Const.mk_tuple_lid
                                        (Prims.parse_int "2")
                                        FStar_Range.dummyRange
                                       in
                                    (uu____1779, (Prims.parse_int "2"),
                                      "tuple2", S)
                                     in
                                  let uu____1780 =
                                    let uu____1791 =
                                      let uu____1800 =
                                        FStar_Reflection_Data.fstar_refl_data_lid
                                          "exp"
                                         in
                                      (uu____1800, (Prims.parse_int "0"),
                                        "exp", R)
                                       in
                                    [uu____1791]  in
                                  uu____1770 :: uu____1780  in
                                (FStar_Parser_Const.option_lid,
                                  (Prims.parse_int "1"), "option", S) ::
                                  uu____1759
                                 in
                              (FStar_Parser_Const.list_lid,
                                (Prims.parse_int "1"), "list", S) ::
                                uu____1748
                               in
                            (FStar_Parser_Const.norm_step_lid,
                              (Prims.parse_int "0"), "norm_step", S) ::
                              uu____1737
                             in
                          uu____1716 :: uu____1726  in
                        uu____1695 :: uu____1705  in
                      uu____1674 :: uu____1684  in
                    uu____1653 :: uu____1663  in
                  (FStar_Parser_Const.string_lid, (Prims.parse_int "0"),
                    "string", S) :: uu____1642
                   in
                (FStar_Parser_Const.unit_lid, (Prims.parse_int "0"), "unit",
                  S) :: uu____1631
                 in
              (FStar_Parser_Const.bool_lid, (Prims.parse_int "0"), "bool", S)
                :: uu____1620
               in
            (FStar_Parser_Const.int_lid, (Prims.parse_int "0"), "int", S) ::
              uu____1609
             in
          let is_known_type_constructor fv1 n1 =
            FStar_Util.for_some
              (fun uu____1933  ->
                 match uu____1933 with
                 | (x,args,uu____1944,uu____1945) ->
                     (FStar_Syntax_Syntax.fv_eq_lid fv1 x) && (n1 = args))
              known_type_constructors
             in
          let find_env_entry bv uu____1956 =
            match uu____1956 with
            | (bv',uu____1962) -> FStar_Syntax_Syntax.bv_eq bv bv'  in
          let rec mk_embedding env t2 =
            let uu____1982 =
              let uu____1983 = FStar_Syntax_Subst.compress t2  in
              uu____1983.FStar_Syntax_Syntax.n  in
            match uu____1982 with
            | FStar_Syntax_Syntax.Tm_name bv when
                FStar_Util.for_some (find_env_entry bv) env ->
                let uu____1991 =
                  let uu____1992 =
                    let uu____1997 =
                      FStar_Util.find_opt (find_env_entry bv) env  in
                    FStar_Util.must uu____1997  in
                  FStar_Pervasives_Native.snd uu____1992  in
                FStar_All.pipe_left mk_any_embedding uu____1991
            | FStar_Syntax_Syntax.Tm_refine (x,uu____2013) ->
                mk_embedding env x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t3,uu____2019,uu____2020) ->
                mk_embedding env t3
            | uu____2061 ->
                let t3 = FStar_TypeChecker_Normalize.unfold_whnf tcenv t2  in
                let uu____2063 = FStar_Syntax_Util.head_and_args t3  in
                (match uu____2063 with
                 | (head1,args) ->
                     let n_args = FStar_List.length args  in
                     let uu____2107 =
                       let uu____2108 = FStar_Syntax_Util.un_uinst head1  in
                       uu____2108.FStar_Syntax_Syntax.n  in
                     (match uu____2107 with
                      | FStar_Syntax_Syntax.Tm_refine (b,uu____2112) ->
                          mk_embedding env b.FStar_Syntax_Syntax.sort
                      | FStar_Syntax_Syntax.Tm_fvar fv1 when
                          is_known_type_constructor fv1 n_args ->
                          let arg_embeddings =
                            FStar_List.map
                              (fun uu____2132  ->
                                 match uu____2132 with
                                 | (t4,uu____2138) -> mk_embedding env t4)
                              args
                             in
                          let nm =
                            (((fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
                             in
                          let uu____2140 =
                            let uu____2149 =
                              FStar_Util.find_opt
                                (fun uu____2173  ->
                                   match uu____2173 with
                                   | (x,uu____2183,uu____2184,uu____2185) ->
                                       FStar_Syntax_Syntax.fv_eq_lid fv1 x)
                                known_type_constructors
                               in
                            FStar_All.pipe_right uu____2149 FStar_Util.must
                             in
                          (match uu____2140 with
                           | (uu____2212,t_arity,trepr_head,loc_embedding) ->
                               let head2 =
                                 mk_basic_embedding loc_embedding nm  in
                               (match t_arity with
                                | _0_44 when _0_44 = (Prims.parse_int "0") ->
                                    head2
                                | n1 ->
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_App
                                         (head2, arg_embeddings))))
                      | uu____2220 ->
                          let uu____2221 =
                            let uu____2222 =
                              let uu____2223 =
                                FStar_Syntax_Print.term_to_string t3  in
                              Prims.strcat "Embedding not defined for type "
                                uu____2223
                               in
                            NoTacticEmbedding uu____2222  in
                          FStar_Exn.raise uu____2221))
             in
          let abstract_tvars tvar_names body =
            match tvar_names with
            | [] -> body
            | uu____2235 ->
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
                  let uu____2272 =
                    let uu____2273 =
                      let uu____2274 =
                        let uu____2281 =
                          let uu____2284 = str_to_name "args_tail"  in
                          [uu____2284]  in
                        (body, uu____2281)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2274  in
                    FStar_All.pipe_left w uu____2273  in
                  (pattern, FStar_Pervasives_Native.None, uu____2272)  in
                let default_branch =
                  let uu____2298 =
                    let uu____2299 =
                      let uu____2300 =
                        let uu____2307 = str_to_name "failwith"  in
                        let uu____2308 =
                          let uu____2311 =
                            let uu____2312 =
                              mlexpr_of_const FStar_Range.dummyRange
                                (FStar_Const.Const_string
                                   ("arity mismatch", FStar_Range.dummyRange))
                               in
                            FStar_All.pipe_left w uu____2312  in
                          [uu____2311]  in
                        (uu____2307, uu____2308)  in
                      FStar_Extraction_ML_Syntax.MLE_App uu____2300  in
                    FStar_All.pipe_left w uu____2299  in
                  (FStar_Extraction_ML_Syntax.MLP_Wild,
                    FStar_Pervasives_Native.None, uu____2298)
                   in
                let body1 =
                  let uu____2318 =
                    let uu____2319 =
                      let uu____2334 = str_to_name "args"  in
                      (uu____2334, [branch1; default_branch])  in
                    FStar_Extraction_ML_Syntax.MLE_Match uu____2319  in
                  FStar_All.pipe_left w uu____2318  in
                mk_lam "args" body1
             in
          let uu____2369 = FStar_Syntax_Util.arrow_formals_comp t1  in
          match uu____2369 with
          | (bs,c) ->
              let result_typ = FStar_Syntax_Util.comp_result c  in
              let arity = FStar_List.length bs  in
              let uu____2410 =
                let uu____2427 =
                  FStar_Util.prefix_until
                    (fun uu____2461  ->
                       match uu____2461 with
                       | (b,uu____2467) ->
                           let uu____2468 =
                             let uu____2469 =
                               FStar_Syntax_Subst.compress
                                 b.FStar_Syntax_Syntax.sort
                                in
                             uu____2469.FStar_Syntax_Syntax.n  in
                           (match uu____2468 with
                            | FStar_Syntax_Syntax.Tm_type uu____2472 -> false
                            | uu____2473 -> true)) bs
                   in
                match uu____2427 with
                | FStar_Pervasives_Native.None  -> (bs, [])
                | FStar_Pervasives_Native.Some (tvars,x,rest) ->
                    (tvars, (x :: rest))
                 in
              (match uu____2410 with
               | (type_vars,bs1) ->
                   let non_tvar_arity = FStar_List.length bs1  in
                   let tvar_names =
                     FStar_List.mapi
                       (fun i  ->
                          fun tv  ->
                            let uu____2656 = FStar_Util.string_of_int i  in
                            Prims.strcat "tv_" uu____2656) type_vars
                      in
                   let tvar_context =
                     FStar_List.map2
                       (fun b  ->
                          fun nm  -> ((FStar_Pervasives_Native.fst b), nm))
                       type_vars tvar_names
                      in
                   let rec aux accum_embeddings env bs2 =
                     match bs2 with
                     | [] ->
                         let arg_unembeddings =
                           FStar_List.rev accum_embeddings  in
                         let res_embedding = mk_embedding env result_typ  in
                         let uu____2742 = FStar_Syntax_Util.is_pure_comp c
                            in
                         if uu____2742
                         then
                           let embed_fun_N =
                             mk_arrow_embedding non_tvar_arity  in
                           let args =
                             let uu____2761 =
                               let uu____2764 =
                                 let uu____2767 = lid_to_top_name fv  in
                                 [uu____2767]  in
                               res_embedding :: uu____2764  in
                             FStar_List.append arg_unembeddings uu____2761
                              in
                           let fun_embedding =
                             FStar_All.pipe_left w
                               (FStar_Extraction_ML_Syntax.MLE_App
                                  (embed_fun_N, args))
                              in
                           let tabs = abstract_tvars tvar_names fun_embedding
                              in
                           let uu____2772 =
                             let uu____2779 = mk_lam "_psc" tabs  in
                             (uu____2779, arity, true)  in
                           FStar_Pervasives_Native.Some uu____2772
                         else
                           (let uu____2791 =
                              let uu____2792 =
                                FStar_TypeChecker_Env.norm_eff_name tcenv
                                  (FStar_Syntax_Util.comp_effect_name c)
                                 in
                              FStar_Ident.lid_equals uu____2792
                                FStar_Parser_Const.effect_TAC_lid
                               in
                            if uu____2791
                            then
                              let h =
                                let uu____2802 =
                                  let uu____2803 =
                                    FStar_Util.string_of_int non_tvar_arity
                                     in
                                  Prims.strcat
                                    "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                                    uu____2803
                                   in
                                str_to_top_name uu____2802  in
                              let tac_fun =
                                let uu____2811 =
                                  let uu____2812 =
                                    let uu____2819 =
                                      let uu____2820 =
                                        let uu____2821 =
                                          FStar_Util.string_of_int
                                            non_tvar_arity
                                           in
                                        Prims.strcat
                                          "FStar_Tactics_Native.from_tactic_"
                                          uu____2821
                                         in
                                      str_to_top_name uu____2820  in
                                    let uu____2828 =
                                      let uu____2831 = lid_to_top_name fv  in
                                      [uu____2831]  in
                                    (uu____2819, uu____2828)  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____2812
                                   in
                                FStar_All.pipe_left w uu____2811  in
                              let tac_lid_app =
                                let uu____2835 =
                                  let uu____2836 =
                                    let uu____2843 =
                                      str_to_top_name
                                        "FStar_Ident.lid_of_str"
                                       in
                                    (uu____2843, [w ml_fv])  in
                                  FStar_Extraction_ML_Syntax.MLE_App
                                    uu____2836
                                   in
                                FStar_All.pipe_left w uu____2835  in
                              let psc = str_to_name "psc"  in
                              let all_args = str_to_name "args"  in
                              let args =
                                let uu____2851 =
                                  let uu____2854 =
                                    FStar_All.pipe_left w
                                      (FStar_Extraction_ML_Syntax.MLE_Const
                                         (FStar_Extraction_ML_Syntax.MLC_Bool
                                            true))
                                     in
                                  [uu____2854; tac_fun]  in
                                FStar_List.append uu____2851
                                  (FStar_List.append arg_unembeddings
                                     [res_embedding; tac_lid_app; psc])
                                 in
                              let tabs =
                                match tvar_names with
                                | [] ->
                                    let uu____2856 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h,
                                             (FStar_List.append args
                                                [all_args])))
                                       in
                                    mk_lam "args" uu____2856
                                | uu____2859 ->
                                    let uu____2862 =
                                      FStar_All.pipe_left w
                                        (FStar_Extraction_ML_Syntax.MLE_App
                                           (h, args))
                                       in
                                    abstract_tvars tvar_names uu____2862
                                 in
                              let uu____2865 =
                                let uu____2872 = mk_lam "psc" tabs  in
                                (uu____2872, (arity + (Prims.parse_int "1")),
                                  false)
                                 in
                              FStar_Pervasives_Native.Some uu____2865
                            else
                              (let uu____2886 =
                                 let uu____2887 =
                                   let uu____2888 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   Prims.strcat
                                     "Plugins not defined for type "
                                     uu____2888
                                    in
                                 NoTacticEmbedding uu____2887  in
                               FStar_Exn.raise uu____2886))
                     | (b,uu____2898)::bs3 ->
                         let uu____2910 =
                           let uu____2913 =
                             mk_embedding env b.FStar_Syntax_Syntax.sort  in
                           uu____2913 :: accum_embeddings  in
                         aux uu____2910 env bs3
                      in
                   (try aux [] tvar_context bs1
                    with
                    | NoTacticEmbedding msg ->
                        ((let uu____2946 = FStar_Ident.string_of_lid fv  in
                          not_implemented_warning t1.FStar_Syntax_Syntax.pos
                            uu____2946 msg);
                         FStar_Pervasives_Native.None)))
  