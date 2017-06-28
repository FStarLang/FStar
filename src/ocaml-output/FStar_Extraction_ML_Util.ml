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
    | FStar_Const.Const_range uu____24 -> failwith "Unsupported constant"
    | FStar_Const.Const_effect  -> failwith "Unsupported constant"
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____40) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (bytes,uu____44) ->
        FStar_Extraction_ML_Syntax.MLC_String
          (FStar_Util.string_of_unicode bytes)
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____47 ->
        failwith "Unhandled constant: reify/reflect"
  
let mlconst_of_const' :
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const c
      with
      | uu____56 ->
          let uu____57 =
            let uu____58 = FStar_Range.string_of_range p  in
            let uu____59 = FStar_Syntax_Print.const_to_string c  in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____58 uu____59
             in
          failwith uu____57
  
let rec subst_aux :
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____73 =
            FStar_Util.find_opt
              (fun uu____79  -> match uu____79 with | (y,uu____83) -> y = x)
              subst1
             in
          (match uu____73 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____94 =
            let uu____98 = subst_aux subst1 t1  in
            let uu____99 = subst_aux subst1 t2  in (uu____98, f, uu____99)
             in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____94
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____104 =
            let uu____108 = FStar_List.map (subst_aux subst1) args  in
            (uu____108, path)  in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____104
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____113 = FStar_List.map (subst_aux subst1) ts  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____113
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
  
let subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____120  ->
    fun args  ->
      match uu____120 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then
            failwith
              "Substitution must be fully applied (see GitHub issue #490)"
          else
            (let uu____130 = FStar_List.zip formals args  in
             subst_aux uu____130 t)
  
let udelta_unfold :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun g  ->
    fun uu___111_140  ->
      match uu___111_140 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____146 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1  in
          (match uu____146 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____150 = subst ts args  in
               FStar_Pervasives_Native.Some uu____150
           | uu____151 -> FStar_Pervasives_Native.None)
      | uu____153 -> FStar_Pervasives_Native.None
  
let eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____160) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____161 -> false
  
let eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___112_166  ->
    match uu___112_166 with
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
        | uu____176 ->
            let uu____179 =
              let uu____180 = FStar_Range.string_of_range r  in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____180
                (eff_to_string f) (eff_to_string f')
               in
            failwith uu____179
  
let join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
  
let mk_ty_fun uu____200 =
  FStar_List.fold_right
    (fun uu____203  ->
       fun t  ->
         match uu____203 with
         | (uu____207,t0) ->
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
                | uu____275 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____293 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let uu____297 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty
                       in
                    FStar_Extraction_ML_Syntax.with_ty uu____297 e1
                 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____304;
                     FStar_Extraction_ML_Syntax.loc = uu____305;_}
                   ->
                   let uu____316 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____316
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____326 = type_leq unfold_ty t2 t2'  in
                        (if uu____326
                         then
                           let body1 =
                             let uu____334 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____334
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let uu____339 =
                             let uu____341 =
                               let uu____342 =
                                 let uu____345 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty
                                    in
                                 FStar_Extraction_ML_Syntax.with_ty uu____345
                                  in
                               FStar_All.pipe_left uu____342
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1))
                                in
                             FStar_Pervasives_Native.Some uu____341  in
                           (true, uu____339)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____361 =
                           let uu____365 =
                             let uu____367 = mk_fun xs body  in
                             FStar_All.pipe_left
                               (fun _0_30  ->
                                  FStar_Pervasives_Native.Some _0_30)
                               uu____367
                              in
                           type_leq_c unfold_ty uu____365 t2 t2'  in
                         match uu____361 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____383 = mk_fun [x] body2  in
                                   FStar_Pervasives_Native.Some uu____383
                               | uu____388 -> FStar_Pervasives_Native.None
                                in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____393 ->
                   let uu____395 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____395
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____419 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____419
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____430 = unfold_ty t  in
                 match uu____430 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____440 = unfold_ty t'  in
                     (match uu____440 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____455 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____455
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____466,uu____467) ->
              let uu____471 = unfold_ty t  in
              (match uu____471 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____481 -> (false, FStar_Pervasives_Native.None))
          | (uu____484,FStar_Extraction_ML_Syntax.MLTY_Named uu____485) ->
              let uu____489 = unfold_ty t'  in
              (match uu____489 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____499 -> (false, FStar_Pervasives_Native.None))
          | uu____502 -> (false, FStar_Pervasives_Native.None)

and type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____510 = type_leq_c g FStar_Pervasives_Native.None t1 t2  in
        FStar_All.pipe_right uu____510 FStar_Pervasives_Native.fst

let is_type_abstraction uu___113_536 =
  match uu___113_536 with
  | (FStar_Util.Inl uu____542,uu____543)::uu____544 -> true
  | uu____556 -> false 
let is_xtuple :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____568  ->
    match uu____568 with
    | (ns,n1) ->
        let uu____577 =
          let uu____578 = FStar_Util.concat_l "." (FStar_List.append ns [n1])
             in
          FStar_Parser_Const.is_tuple_datacon_string uu____578  in
        if uu____577
        then
          let uu____580 =
            let uu____581 = FStar_Util.char_at n1 (Prims.parse_int "7")  in
            FStar_Util.int_of_char uu____581  in
          FStar_Pervasives_Native.Some uu____580
        else FStar_Pervasives_Native.None
  
let resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____590 = is_xtuple mlp  in
        (match uu____590 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____593 -> e)
    | uu____595 -> e
  
let record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___114_600  ->
    match uu___114_600 with
    | f::uu____604 ->
        let uu____606 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____606 with
         | (ns,uu____612) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____618 -> failwith "impos"
  
let record_fields fs vs =
  FStar_List.map2
    (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e)) fs
    vs
  
let is_xtuple_ty :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____650  ->
    match uu____650 with
    | (ns,n1) ->
        let uu____659 =
          let uu____660 = FStar_Util.concat_l "." (FStar_List.append ns [n1])
             in
          FStar_Parser_Const.is_tuple_constructor_string uu____660  in
        if uu____659
        then
          let uu____662 =
            let uu____663 = FStar_Util.char_at n1 (Prims.parse_int "5")  in
            FStar_Util.int_of_char uu____663  in
          FStar_Pervasives_Native.Some uu____662
        else FStar_Pervasives_Native.None
  
let resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____672 = is_xtuple_ty mlp  in
        (match uu____672 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____675 -> t)
    | uu____677 -> t
  
let codegen_fsharp : Prims.unit -> Prims.bool =
  fun uu____680  ->
    let uu____681 =
      let uu____682 = FStar_Options.codegen ()  in FStar_Option.get uu____682
       in
    uu____681 = "FSharp"
  
let flatten_ns : Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____689 = codegen_fsharp ()  in
    if uu____689
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let flatten_mlpath :
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string
  =
  fun uu____696  ->
    match uu____696 with
    | (ns,n1) ->
        let uu____704 = codegen_fsharp ()  in
        if uu____704
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
  
let mlpath_of_lid :
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____712 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (uu____712, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____728 = unfold_ty t  in
         match uu____728 with
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
            let uu____747 =
              let uu____751 = eraseTypeDeep unfold_ty tyd  in
              let uu____755 = eraseTypeDeep unfold_ty tycd  in
              (uu____751, etag, uu____755)  in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____747
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____764 = erasableType unfold_ty t  in
          if uu____764
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____769 =
               let uu____773 = FStar_List.map (eraseTypeDeep unfold_ty) lty
                  in
               (uu____773, mlp)  in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____769)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____781 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____781
      | uu____786 -> t
  
let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr =
  let uu____788 =
    let uu____791 =
      (mk_ty_fun ())
        [(("x", (Prims.parse_int "0")),
           FStar_Extraction_ML_Syntax.ml_bool_ty);
        (("y", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty
       in
    FStar_Extraction_ML_Syntax.with_ty uu____791  in
  FStar_All.pipe_left uu____788
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
          let uu____844 = conjoin x y  in
          FStar_Pervasives_Native.Some uu____844
  
let mlloc_of_range :
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let uu____852 = FStar_Range.file_of_range r  in (line, uu____852)
  
let rec argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____860,b) ->
        let uu____862 = argTypes b  in a :: uu____862
    | uu____864 -> []
  
let rec uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____875,b) ->
        let uu____877 = uncurry_mlty_fun b  in
        (match uu____877 with | (args,res) -> ((a :: args), res))
    | uu____889 -> ([], t)
  