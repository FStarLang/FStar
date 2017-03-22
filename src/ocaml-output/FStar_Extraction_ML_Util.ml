open Prims
let pruneNones l =
  FStar_List.fold_right
    (fun x  -> fun ll  -> match x with | Some xs -> xs :: ll | None  -> ll) l
    []
  
let mlconst_of_const :
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant =
  fun sctt  ->
    match sctt with
    | FStar_Const.Const_range _|FStar_Const.Const_effect  ->
        failwith "Unsupported constant"
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
    | FStar_Const.Const_reify |FStar_Const.Const_reflect _ ->
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
          failwith
            (let _0_209 = FStar_Range.string_of_range p  in
             let _0_208 = FStar_Syntax_Print.const_to_string c  in
             FStar_Util.format2 "(%s) Failed to translate constant %s "
               _0_209 _0_208)
  
let rec subst_aux :
  (FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____70 =
            FStar_Util.find_opt
              (fun uu____76  -> match uu____76 with | (y,uu____80) -> y = x)
              subst
             in
          (match uu____70 with | Some ts -> Prims.snd ts | None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          FStar_Extraction_ML_Syntax.MLTY_Fun
            (let _0_211 = subst_aux subst t1  in
             let _0_210 = subst_aux subst t2  in (_0_211, f, _0_210))
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          FStar_Extraction_ML_Syntax.MLTY_Named
            (let _0_212 = FStar_List.map (subst_aux subst) args  in
             (_0_212, path))
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          FStar_Extraction_ML_Syntax.MLTY_Tuple
            (FStar_List.map (subst_aux subst) ts)
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
  
let subst :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____103  ->
    fun args  ->
      match uu____103 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then
            failwith
              "Substitution must be fully applied (see GitHub issue #490)"
          else
            (let _0_213 = FStar_List.zip formals args  in subst_aux _0_213 t)
  
let udelta_unfold :
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty Prims.option
  =
  fun g  ->
    fun uu___109_119  ->
      match uu___109_119 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n) ->
          let uu____125 = FStar_Extraction_ML_UEnv.lookup_ty_const g n  in
          (match uu____125 with
           | Some ts -> Some (subst ts args)
           | uu____129 -> None)
      | uu____131 -> None
  
let eff_leq :
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____138) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____139 -> false
  
let eff_to_string : FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___110_144  ->
    match uu___110_144 with
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
           ,FStar_Extraction_ML_Syntax.E_PURE )
          |(FStar_Extraction_ML_Syntax.E_PURE
            ,FStar_Extraction_ML_Syntax.E_IMPURE )
           |(FStar_Extraction_ML_Syntax.E_IMPURE
             ,FStar_Extraction_ML_Syntax.E_IMPURE )
            -> FStar_Extraction_ML_Syntax.E_IMPURE
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
        | uu____154 ->
            failwith
              (let _0_214 = FStar_Range.string_of_range r  in
               FStar_Util.format3
                 "Impossible (%s): Inconsistent effects %s and %s" _0_214
                 (eff_to_string f) (eff_to_string f'))
  
let join_l :
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
  
let mk_ty_fun uu____176 =
  FStar_List.fold_right
    (fun uu____179  ->
       fun t  ->
         match uu____179 with
         | (uu____183,t0) ->
             FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
  
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.option
let rec type_leq_c :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr Prims.option)
  =
  fun unfold_ty  ->
    fun e  ->
      fun t  ->
        fun t'  ->
          match (t, t') with
          | (FStar_Extraction_ML_Syntax.MLTY_Var
             x,FStar_Extraction_ML_Syntax.MLTY_Var y) ->
              if (Prims.fst x) = (Prims.fst y)
              then (true, e)
              else (false, None)
          | (FStar_Extraction_ML_Syntax.MLTY_Fun
             (t1,f,t2),FStar_Extraction_ML_Syntax.MLTY_Fun (t1',f',t2')) ->
              let mk_fun xs body =
                match xs with
                | [] -> body
                | uu____251 ->
                    let e =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body)
                      | uu____269 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body)
                       in
                    let _0_215 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty
                       in
                    FStar_Extraction_ML_Syntax.with_ty _0_215 e
                 in
              (match e with
               | Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____279;
                     FStar_Extraction_ML_Syntax.loc = uu____280;_}
                   ->
                   let uu____291 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f')  in
                   if uu____291
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____301 = type_leq unfold_ty t2 t2'  in
                        (if uu____301
                         then
                           let body =
                             let uu____309 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty
                                in
                             if uu____309
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2'))
                              in
                           let _0_217 =
                             Some
                               (let _0_216 =
                                  FStar_Extraction_ML_Syntax.with_ty
                                    ((mk_ty_fun ()) [x]
                                       body.FStar_Extraction_ML_Syntax.mlty)
                                   in
                                FStar_All.pipe_left _0_216
                                  (FStar_Extraction_ML_Syntax.MLE_Fun
                                     ([x], body)))
                              in
                           (true, _0_217)
                         else (false, None))
                      else
                        (let uu____329 =
                           let _0_220 =
                             let _0_219 = mk_fun xs body  in
                             FStar_All.pipe_left (fun _0_218  -> Some _0_218)
                               _0_219
                              in
                           type_leq_c unfold_ty _0_220 t2 t2'  in
                         match uu____329 with
                         | (ok,body) ->
                             let res =
                               match body with
                               | Some body -> Some (mk_fun [x] body)
                               | uu____352 -> None  in
                             (ok, res)))
                   else (false, None)
               | uu____357 ->
                   let uu____359 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2')
                      in
                   if uu____359 then (true, e) else (false, None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____383 =
                  FStar_List.forall2 (type_leq unfold_ty) args args'  in
                (if uu____383 then (true, e) else (false, None))
              else
                (let uu____394 = unfold_ty t  in
                 match uu____394 with
                 | Some t -> type_leq_c unfold_ty e t t'
                 | None  ->
                     let uu____404 = unfold_ty t'  in
                     (match uu____404 with
                      | None  -> (false, None)
                      | Some t' -> type_leq_c unfold_ty e t t'))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____419 = FStar_List.forall2 (type_leq unfold_ty) ts ts'
                 in
              if uu____419 then (true, e) else (false, None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____430,uu____431) ->
              let uu____435 = unfold_ty t  in
              (match uu____435 with
               | Some t -> type_leq_c unfold_ty e t t'
               | uu____445 -> (false, None))
          | (uu____448,FStar_Extraction_ML_Syntax.MLTY_Named uu____449) ->
              let uu____453 = unfold_ty t'  in
              (match uu____453 with
               | Some t' -> type_leq_c unfold_ty e t t'
               | uu____463 -> (false, None))
          | uu____466 -> (false, None)

and type_leq :
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let _0_221 = type_leq_c g None t1 t2  in
        FStar_All.pipe_right _0_221 Prims.fst

let is_type_abstraction uu___111_496 =
  match uu___111_496 with
  | (FStar_Util.Inl uu____502,uu____503)::uu____504 -> true
  | uu____516 -> false 
let is_xtuple :
  (Prims.string Prims.list * Prims.string) -> Prims.int Prims.option =
  fun uu____528  ->
    match uu____528 with
    | (ns,n) ->
        if ns = ["Prims"]
        then
          (match n with
           | "Mktuple2" -> Some (Prims.parse_int "2")
           | "Mktuple3" -> Some (Prims.parse_int "3")
           | "Mktuple4" -> Some (Prims.parse_int "4")
           | "Mktuple5" -> Some (Prims.parse_int "5")
           | "Mktuple6" -> Some (Prims.parse_int "6")
           | "Mktuple7" -> Some (Prims.parse_int "7")
           | "Mktuple8" -> Some (Prims.parse_int "8")
           | uu____540 -> None)
        else None
  
let resugar_exp :
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        (match is_xtuple mlp with
         | Some n ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____550 -> e)
    | uu____552 -> e
  
let record_field_path :
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___112_557  ->
    match uu___112_557 with
    | f::uu____561 ->
        let uu____563 = FStar_Util.prefix f.FStar_Ident.ns  in
        (match uu____563 with
         | (ns,uu____569) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____575 -> failwith "impos"
  
let record_fields fs vs =
  FStar_List.map2
    (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e)) fs
    vs
  
let is_xtuple_ty :
  (Prims.string Prims.list * Prims.string) -> Prims.int Prims.option =
  fun uu____607  ->
    match uu____607 with
    | (ns,n) ->
        if ns = ["Prims"]
        then
          (match n with
           | "tuple2" -> Some (Prims.parse_int "2")
           | "tuple3" -> Some (Prims.parse_int "3")
           | "tuple4" -> Some (Prims.parse_int "4")
           | "tuple5" -> Some (Prims.parse_int "5")
           | "tuple6" -> Some (Prims.parse_int "6")
           | "tuple7" -> Some (Prims.parse_int "7")
           | "tuple8" -> Some (Prims.parse_int "8")
           | uu____619 -> None)
        else None
  
let resugar_mlty :
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        (match is_xtuple_ty mlp with
         | Some n -> FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____629 -> t)
    | uu____631 -> t
  
let codegen_fsharp : Prims.unit -> Prims.bool =
  fun uu____634  ->
    let _0_222 = FStar_Option.get (FStar_Options.codegen ())  in
    _0_222 = "FSharp"
  
let flatten_ns : Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____640 = codegen_fsharp ()  in
    if uu____640
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
  
let flatten_mlpath : (Prims.string Prims.list * Prims.string) -> Prims.string
  =
  fun uu____647  ->
    match uu____647 with
    | (ns,n) ->
        let uu____655 = codegen_fsharp ()  in
        if uu____655
        then FStar_String.concat "." (FStar_List.append ns [n])
        else FStar_String.concat "_" (FStar_List.append ns [n])
  
let mlpath_of_lid :
  FStar_Ident.lident -> (Prims.string Prims.list * Prims.string) =
  fun l  ->
    let _0_223 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText))
       in
    (_0_223, ((l.FStar_Ident.ident).FStar_Ident.idText))
  
let rec erasableType :
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____677 = unfold_ty t  in
         match uu____677 with
         | Some t -> erasableType unfold_ty t
         | None  -> false)
  
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
            FStar_Extraction_ML_Syntax.MLTY_Fun
              (let _0_225 = eraseTypeDeep unfold_ty tyd  in
               let _0_224 = eraseTypeDeep unfold_ty tycd  in
               (_0_225, etag, _0_224))
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____707 = erasableType unfold_ty t  in
          if uu____707
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            FStar_Extraction_ML_Syntax.MLTY_Named
              ((let _0_226 = FStar_List.map (eraseTypeDeep unfold_ty) lty  in
                (_0_226, mlp)))
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          FStar_Extraction_ML_Syntax.MLTY_Tuple
            (FStar_List.map (eraseTypeDeep unfold_ty) lty)
      | uu____721 -> t
  
let prims_op_equality : FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
  
let prims_op_amp_amp : FStar_Extraction_ML_Syntax.mlexpr =
  let _0_227 =
    FStar_Extraction_ML_Syntax.with_ty
      ((mk_ty_fun ())
         [(("x", (Prims.parse_int "0")),
            FStar_Extraction_ML_Syntax.ml_bool_ty);
         (("y", (Prims.parse_int "0")),
           FStar_Extraction_ML_Syntax.ml_bool_ty)]
         FStar_Extraction_ML_Syntax.ml_bool_ty)
     in
  FStar_All.pipe_left _0_227
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
  FStar_Extraction_ML_Syntax.mlexpr Prims.option ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.option ->
      FStar_Extraction_ML_Syntax.mlexpr Prims.option
  =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (None ,None ) -> None
      | (Some x,None )|(None ,Some x) -> Some x
      | (Some x,Some y) -> Some (conjoin x y)
  
let mlloc_of_range : FStar_Range.range -> (Prims.int * Prims.string) =
  fun r  ->
    let pos = FStar_Range.start_of_range r  in
    let line = FStar_Range.line_of_pos pos  in
    let _0_228 = FStar_Range.file_of_range r  in (line, _0_228)
  
let rec argTypes :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____788,b) ->
        let _0_229 = argTypes b  in a :: _0_229
    | uu____790 -> []
  
let rec uncurry_mlty_fun :
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list *
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____801,b) ->
        let uu____803 = uncurry_mlty_fun b  in
        (match uu____803 with | (args,res) -> ((a :: args), res))
    | uu____815 -> ([], t)
  