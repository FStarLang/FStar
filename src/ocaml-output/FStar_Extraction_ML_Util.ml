open Prims
let pruneNones l =
  FStar_List.fold_right
    (fun x  ->
       fun ll  ->
         match x with
         | FStar_Pervasives_Native.Some xs -> xs :: ll
         | FStar_Pervasives_Native.None  -> ll) l []
  
let mlconst_of_const :
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant =
  fun sctt  ->
    match sctt with
    | FStar_Const.Const_range uu____30 -> failwith "Unsupported constant"
    | FStar_Const.Const_effect  -> failwith "Unsupported constant"
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____46) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (bytes,uu____50) ->
        FStar_Extraction_ML_Syntax.MLC_String
          (FStar_Util.string_of_unicode bytes)
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____53 ->
        failwith "Unhandled constant: reify/reflect"
  
let mlconst_of_const' :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const c
      with
      | uu____68 ->
          let uu____69 =
            let uu____70 = FStar_Range.string_of_range p  in
            let uu____71 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____70 uu____71
             in
          failwith uu____69
  
let rec subst_aux :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____87 =
            FStar_Util.find_opt
              (fun uu____96  -> match uu____96 with | (y,uu____100) -> y = x)
              subst1
             in
          (match uu____87 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____111 =
            let uu____115 = subst_aux subst1 t1  in
            let uu____116 = subst_aux subst1 t2  in (uu____115, f, uu____116)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____111
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____121 =
            let uu____125 = FStar_List.map (subst_aux subst1) args  in
            (uu____125, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____121
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____130 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____130
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
  
let subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____139  ->
    fun args  ->
      match uu____139 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then
            failwith
              "Substitution must be fully applied (see GitHub issue #490)"
          else
            (let uu____153 = FStar_List.zip formals args  in
             subst_aux uu____153 t)
  
let udelta_unfold :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun g  ->
    fun uu___112_165  ->
      match uu___112_165 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____171 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____171 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____175 = subst ts args  in
               FStar_Pervasives_Native.Some uu____175
           | uu____176 -> FStar_Pervasives_Native.None)
      | uu____178 -> FStar_Pervasives_Native.None
  
let eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____187) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____188 -> false
  
let eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___113_194  ->
    match uu___113_194 with
    | FStar_Extraction_ML_Syntax.E_PURE  -> "Pure"
    | FStar_Extraction_ML_Syntax.E_GHOST  -> "Ghost"
    | FStar_Extraction_ML_Syntax.E_IMPURE  -> "Impure"
  
let join :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.e_tag -> FStar_Extraction_ML_Syntax.e_tag
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
        | uu____207 ->
            let uu____210 =
              let uu____211 = FStar_Range.string_of_range r  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____211
                (eff_to_string f) (eff_to_string f')
               in
            failwith uu____210
  
let join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
  
let mk_ty_fun uu____236 =
  FStar_List.fold_right
    (fun uu____243  ->
       fun t  ->
         match uu____243 with
         | (uu____247,t0) ->
             FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
  
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
let rec type_leq_c :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2
  =
  fun unfold_ty  ->
    fun e  ->
      fun t  ->
        fun t'  ->
          match (t, t') with
          | (FStar_Extraction_ML_Syntax.MLTY_Var
             x,FStar_Extraction_ML_Syntax.MLTY_Var y) ->
              if
                (FStar_Pervasives_Native.fst x) =
                  (FStar_Pervasives_Native.fst y)
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Fun
             (t1,f,t2),FStar_Extraction_ML_Syntax.MLTY_Fun (t1',f',t2')) ->
              let mk_fun xs body =
                match xs with
                | [] -> body
                | uu____312 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____330 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____334 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty
                       in
                    FStar_Extraction_ML_Syntax.with_ty uu____334 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____341;
                     FStar_Extraction_ML_Syntax.loc = uu____342;_}
                   ->
                   let uu____353 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____353
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____363 = type_leq unfold_ty t2 t2'  in
                        (if uu____363
                         then
                           let body1 =
                             let uu____371 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____371
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____376 =
                             let uu____378 =
                               let uu____379 =
                                 let uu____382 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____382
                                  in
                               FStar_All.pipe_left uu____379
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____378  in
                           (true, uu____376)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____398 =
                           let uu____402 =
                             let uu____404 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_40  ->
                                  FStar_Pervasives_Native.Some _0_40)
                               uu____404
                              in
                           type_leq_c unfold_ty uu____402 t2 t2'  in
                         match uu____398 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____420 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____420
                               | uu____425 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____430 ->
                   let uu____432 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____432
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____456 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____456
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____467 = unfold_ty t  in
                 match uu____467 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____477 = unfold_ty t'  in
                     (match uu____477 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____492 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____492
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____503,uu____504) ->
              let uu____508 = unfold_ty t  in
              (match uu____508 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____518 -> (false, FStar_Pervasives_Native.None))
          | (uu____521,FStar_Extraction_ML_Syntax.MLTY_Named uu____522) ->
              let uu____526 = unfold_ty t'  in
              (match uu____526 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____536 -> (false, FStar_Pervasives_Native.None))
          | uu____539 -> (false, FStar_Pervasives_Native.None)

and type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____547 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____547 FStar_Pervasives_Native.fst

let is_type_abstraction uu___114_577 =
  match uu___114_577 with
  | (FStar_Util.Inl uu____583,uu____584)::uu____585 -> true
  | uu____597 -> false 
let is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____610  ->
    match uu____610 with
    | (ns,n1) ->
        let uu____619 =
          let uu____620 = FStar_Util.concat_l "." (FStar_List.append ns [n1])
             in
          FStar_Parser_Const.is_tuple_datacon_string uu____620  in
        if uu____619
        then
          let uu____622 =
            let uu____623 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____623  in
          FStar_Pervasives_Native.Some uu____622
        else FStar_Pervasives_Native.None
  
let resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____633 = is_xtuple mlp  in
        (match uu____633 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____636 -> e)
    | uu____638 -> e
  
let record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___115_644  ->
    match uu___115_644 with
    | f::uu____648 ->
        let uu____650 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____650 with
         | (ns,uu____656) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____663 -> failwith "impos"
  
let record_fields fs vs =
  FStar_List.map2
    (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e)) fs
    vs
  
let is_xtuple_ty :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____701  ->
    match uu____701 with
    | (ns,n1) ->
        let uu____710 =
          let uu____711 = FStar_Util.concat_l "." (FStar_List.append ns [n1])
             in
          FStar_Parser_Const.is_tuple_constructor_string uu____711  in
        if uu____710
        then
          let uu____713 =
            let uu____714 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____714  in
          FStar_Pervasives_Native.Some uu____713
        else FStar_Pervasives_Native.None
  
let resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____724 = is_xtuple_ty mlp  in
        (match uu____724 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____727 -> t)
    | uu____729 -> t
  
let codegen_fsharp : Prims.unit -> Prims.bool =
  fun uu____733  ->
    let uu____734 =
      let uu____735 = FStar_Options.codegen ()  in FStar_Option.get uu____735
       in
    uu____734 = "FSharp"
  
let flatten_ns : Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____743 = codegen_fsharp ()  in
    if uu____743
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string
  =
  fun uu____751  ->
    match uu____751 with
    | (ns,n1) ->
        let uu____759 = codegen_fsharp ()  in
        if uu____759
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____768 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____768, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____787 = unfold_ty t  in
         match uu____787 with
         | FStar_Pervasives_Native.Some t1 -> erasableType unfold_ty t1
         | FStar_Pervasives_Native.None  -> false)
  
let rec eraseTypeDeep :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun unfold_ty  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Fun (tyd,etag,tycd) ->
          if etag = FStar_Extraction_ML_Syntax.E_PURE
          then
            let uu____808 =
              let uu____812 = eraseTypeDeep unfold_ty tyd  in
              let uu____816 = eraseTypeDeep unfold_ty tycd  in
              (uu____812, etag, uu____816)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____808
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____825 = erasableType unfold_ty t  in
          if uu____825
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____830 =
               let uu____834 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____834, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____830)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____842 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____842
      | uu____847 -> t
  
let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr =
  let uu____849 =
    let uu____852 =
      (mk_ty_fun ())
        [(("x", (Prims.parse_int "0")),
           FStar_Extraction_ML_Syntax.ml_bool_ty);
        (("y", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____852  in
  FStar_All.pipe_left uu____849
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_AmpAmp"))
  
let conjoin :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun e1  ->
    fun e2  ->
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_bool_ty)
        (FStar_Extraction_ML_Syntax.MLE_App (prims_op_amp_amp, [e1; e2]))
  
let conjoin_opt :
  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option
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
          let uu____909 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____909
  
let mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____918 = FStar_Range.file_of_range r  in (line, uu____918)
  
let rec argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____926,b) ->
        let uu____928 = argTypes b  in a :: uu____928
    | uu____930 -> []
  
let rec uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____942,b) ->
        let uu____944 = uncurry_mlty_fun b  in
        (match uu____944 with | (args,res) -> ((a :: args), res))
    | uu____956 -> ([], t)
  
type emb_decl =
  | Embed 
  | Unembed 
let uu___is_Embed : emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____962 -> false
  
let uu___is_Unembed : emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____967 -> false
  
let lid_to_name : FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun l  ->
    let uu____972 = FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
    FStar_Extraction_ML_Syntax.MLE_Name uu____972
  
let lid_to_top_name : FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun l  ->
    let uu____977 =
      let uu____978 = FStar_Extraction_ML_Syntax.mlpath_of_lident l  in
      FStar_Extraction_ML_Syntax.MLE_Name uu____978  in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____977
  
let str_to_name : Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  ->
    let uu____983 = FStar_Ident.lid_of_str s  in lid_to_name uu____983
  
let str_to_top_name : Prims.string -> FStar_Extraction_ML_Syntax.mlexpr =
  fun s  ->
    let uu____988 = FStar_Ident.lid_of_str s  in lid_to_top_name uu____988
  
let fstar_tc_common_prefix :
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_TypeChecker_Common." s) 
let fstar_refl_basic_prefix :
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Basic." s) 
let fstar_refl_data_prefix :
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Data." s) 
let mk_embedding :
  emb_decl -> Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun m  ->
    fun s  ->
      match m with
      | Embed  -> fstar_refl_basic_prefix (Prims.strcat "embed_" s)
      | Unembed  -> fstar_refl_basic_prefix (Prims.strcat "unembed_" s)
  
let rec mk_tac_param_type :
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun t  ->
    let uu____1013 =
      let uu____1014 = FStar_Syntax_Subst.compress t  in
      uu____1014.FStar_Syntax_Syntax.n  in
    match uu____1013 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
        fstar_tc_common_prefix "t_int"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
        fstar_tc_common_prefix "t_bool"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
        fstar_tc_common_prefix "t_unit"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid ->
        fstar_tc_common_prefix "t_string"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1022 = FStar_Reflection_Data.fstar_refl_types_lid "binder"
           in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1022 ->
        fstar_refl_data_prefix "t_binder"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1024 = FStar_Reflection_Data.fstar_refl_types_lid "term"
           in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1024 ->
        fstar_refl_data_prefix "t_term"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1026 = FStar_Reflection_Data.fstar_refl_types_lid "fv"  in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1026 ->
        fstar_refl_data_prefix "t_fv"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1028 = FStar_Reflection_Data.fstar_refl_syntax_lid "binder"
           in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1028 ->
        fstar_refl_data_prefix "t_binders"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1030 =
          FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step"  in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1030 ->
        fstar_refl_data_prefix "t_norm_step"
    | FStar_Syntax_Syntax.Tm_app (h,args) ->
        let uu____1047 =
          let uu____1048 = FStar_Syntax_Subst.compress h  in
          uu____1048.FStar_Syntax_Syntax.n  in
        (match uu____1047 with
         | FStar_Syntax_Syntax.Tm_uinst (h',uu____1052) ->
             let uu____1057 =
               let uu____1058 = FStar_Syntax_Subst.compress h'  in
               uu____1058.FStar_Syntax_Syntax.n  in
             (match uu____1057 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.list_lid
                  ->
                  let arg_term =
                    let uu____1065 = FStar_List.hd args  in
                    FStar_Pervasives_Native.fst uu____1065  in
                  let uu____1076 =
                    let uu____1080 =
                      let uu____1081 = fstar_tc_common_prefix "t_list_of"  in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1081
                       in
                    let uu____1082 =
                      let uu____1084 =
                        let uu____1086 = mk_tac_param_type arg_term  in
                        [uu____1086]  in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1084
                       in
                    (uu____1080, uu____1082)  in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1076
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.option_lid
                  ->
                  let arg_term =
                    let uu____1092 = FStar_List.hd args  in
                    FStar_Pervasives_Native.fst uu____1092  in
                  let uu____1103 =
                    let uu____1107 =
                      let uu____1108 = fstar_tc_common_prefix "t_option_of"
                         in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1108
                       in
                    let uu____1109 =
                      let uu____1111 =
                        let uu____1113 = mk_tac_param_type arg_term  in
                        [uu____1113]  in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1111
                       in
                    (uu____1107, uu____1109)  in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1103
              | uu____1115 ->
                  let uu____1116 =
                    let uu____1117 =
                      let uu____1118 = FStar_Syntax_Subst.compress h'  in
                      FStar_Syntax_Print.term_to_string uu____1118  in
                    Prims.strcat
                      "Type term not defined for higher-order type "
                      uu____1117
                     in
                  failwith uu____1116)
         | uu____1119 -> failwith "Impossible")
    | uu____1120 ->
        let uu____1121 =
          let uu____1122 =
            let uu____1123 = FStar_Syntax_Subst.compress t  in
            FStar_Syntax_Print.term_to_string uu____1123  in
          Prims.strcat "Type term not defined for " uu____1122  in
        failwith uu____1121
  
let rec mk_tac_embedding_path :
  emb_decl -> FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun m  ->
    fun t  ->
      let uu____1132 =
        let uu____1133 = FStar_Syntax_Subst.compress t  in
        uu____1133.FStar_Syntax_Syntax.n  in
      match uu____1132 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
          mk_embedding m "int"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
          mk_embedding m "bool"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
          mk_embedding m "unit"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid ->
          mk_embedding m "string"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1141 =
            FStar_Reflection_Data.fstar_refl_types_lid "binder"  in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1141 ->
          mk_embedding m "binder"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1143 = FStar_Reflection_Data.fstar_refl_types_lid "term"
             in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1143 ->
          mk_embedding m "term"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1145 = FStar_Reflection_Data.fstar_refl_types_lid "fv"
             in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1145 ->
          mk_embedding m "fvar"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1147 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "binders"  in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1147 ->
          mk_embedding m "binders"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1149 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step"  in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1149 ->
          mk_embedding m "norm_step"
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____1166 =
            let uu____1167 = FStar_Syntax_Subst.compress h  in
            uu____1167.FStar_Syntax_Syntax.n  in
          (match uu____1166 with
           | FStar_Syntax_Syntax.Tm_uinst (h',uu____1171) ->
               let uu____1176 =
                 let uu____1181 =
                   let uu____1182 = FStar_Syntax_Subst.compress h'  in
                   uu____1182.FStar_Syntax_Syntax.n  in
                 match uu____1181 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.list_lid
                     ->
                     let arg_term =
                       let uu____1193 = FStar_List.hd args  in
                       FStar_Pervasives_Native.fst uu____1193  in
                     let uu____1204 =
                       let uu____1206 = mk_tac_embedding_path m arg_term  in
                       [uu____1206]  in
                     let uu____1207 = mk_tac_param_type arg_term  in
                     ("list", uu____1204, uu____1207)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.option_lid
                     ->
                     let arg_term =
                       let uu____1213 = FStar_List.hd args  in
                       FStar_Pervasives_Native.fst uu____1213  in
                     let uu____1224 =
                       let uu____1226 = mk_tac_embedding_path m arg_term  in
                       [uu____1226]  in
                     let uu____1227 = mk_tac_param_type arg_term  in
                     ("option", uu____1224, uu____1227)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.tactic_lid
                     -> failwith "Embedding for tactics not defined"
                 | uu____1234 ->
                     let uu____1235 =
                       let uu____1236 =
                         let uu____1237 = FStar_Syntax_Subst.compress h'  in
                         FStar_Syntax_Print.term_to_string uu____1237  in
                       Prims.strcat
                         "Embedding not defined for higher-order type "
                         uu____1236
                        in
                     failwith uu____1235
                  in
               (match uu____1176 with
                | (ht,hargs,type_arg) ->
                    let hargs1 =
                      match m with
                      | Embed  -> FStar_List.append hargs [type_arg]
                      | Unembed  -> hargs  in
                    let uu____1250 =
                      let uu____1254 =
                        let uu____1255 = mk_embedding m ht  in
                        FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top uu____1255
                         in
                      let uu____1256 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) hargs1
                         in
                      (uu____1254, uu____1256)  in
                    FStar_Extraction_ML_Syntax.MLE_App uu____1250)
           | uu____1259 -> failwith "Impossible")
      | uu____1260 ->
          let uu____1261 =
            let uu____1262 =
              let uu____1263 = FStar_Syntax_Subst.compress t  in
              FStar_Syntax_Print.term_to_string uu____1263  in
            Prims.strcat "Embedding not defined for type " uu____1262  in
          failwith uu____1261
  
let mk_interpretation_fun tac_lid assm_lid t bs =
  let arg_types =
    FStar_List.map
      (fun x  -> (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort) bs
     in
  let arity = FStar_List.length bs  in
  let h =
    let uu____1315 =
      let uu____1316 = FStar_Util.string_of_int arity  in
      Prims.strcat "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
        uu____1316
       in
    str_to_top_name uu____1315  in
  let tac_fun =
    let uu____1324 =
      let uu____1328 =
        let uu____1329 =
          let uu____1330 = FStar_Util.string_of_int arity  in
          Prims.strcat "FStar_Tactics_Native.from_tactic_" uu____1330  in
        str_to_top_name uu____1329  in
      let uu____1337 =
        let uu____1339 = lid_to_top_name tac_lid  in [uu____1339]  in
      (uu____1328, uu____1337)  in
    FStar_Extraction_ML_Syntax.MLE_App uu____1324  in
  let tac_lid_app =
    let uu____1342 =
      let uu____1346 = str_to_top_name "FStar_Ident.lid_of_str"  in
      (uu____1346,
        [FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top assm_lid])
       in
    FStar_Extraction_ML_Syntax.MLE_App uu____1342  in
  let args =
    let uu____1350 =
      let uu____1352 = str_to_name "ps"  in [uu____1352; tac_fun]  in
    let uu____1353 =
      let uu____1355 =
        FStar_List.map (mk_tac_embedding_path Unembed) arg_types  in
      let uu____1357 =
        let uu____1359 = mk_tac_embedding_path Embed t  in
        let uu____1360 =
          let uu____1362 = mk_tac_param_type t  in
          let uu____1363 =
            let uu____1365 =
              let uu____1367 = str_to_name "args"  in [uu____1367]  in
            tac_lid_app :: uu____1365  in
          uu____1362 :: uu____1363  in
        uu____1359 :: uu____1360  in
      FStar_List.append uu____1355 uu____1357  in
    FStar_List.append uu____1350 uu____1353  in
  let app =
    let uu____1369 =
      let uu____1370 =
        let uu____1374 =
          FStar_List.map
            (FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.MLTY_Top) args
           in
        (h, uu____1374)  in
      FStar_Extraction_ML_Syntax.MLE_App uu____1370  in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1369
     in
  FStar_Extraction_ML_Syntax.MLE_Fun
    ([(("ps", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.MLTY_Top);
     (("args", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.MLTY_Top)],
      app)
  