open Prims
let pruneNones l =
  FStar_List.fold_right
    (fun x  -> fun ll  -> match x with | Some xs -> xs :: ll | None  -> ll) l
    []
let mlconst_of_const:
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant =
  fun sctt  ->
    match sctt with
    | FStar_Const.Const_range uu____27 -> failwith "Unsupported constant"
    | FStar_Const.Const_effect  -> failwith "Unsupported constant"
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____43) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (bytes,uu____47) ->
        FStar_Extraction_ML_Syntax.MLC_String
          (FStar_Util.string_of_unicode bytes)
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____50 ->
        failwith "Unhandled constant: reify/reflect"
let mlconst_of_const':
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const c
      with
      | uu____63 ->
          let uu____64 =
            let uu____65 = FStar_Range.string_of_range p in
            let uu____66 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____65 uu____66 in
          failwith uu____64
let rec subst_aux:
  (FStar_Extraction_ML_Syntax.mlident* FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____80 =
            FStar_Util.find_opt
              (fun uu____89  -> match uu____89 with | (y,uu____93) -> y = x)
              subst1 in
          (match uu____80 with | Some ts -> snd ts | None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____104 =
            let uu____108 = subst_aux subst1 t1 in
            let uu____109 = subst_aux subst1 t2 in (uu____108, f, uu____109) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____104
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____114 =
            let uu____118 = FStar_List.map (subst_aux subst1) args in
            (uu____118, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____114
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____123 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____123
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____130  ->
    fun args  ->
      match uu____130 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then
            failwith
              "Substitution must be fully applied (see GitHub issue #490)"
          else
            (let uu____140 = FStar_List.zip formals args in
             subst_aux uu____140 t)
let udelta_unfold:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty option
  =
  fun g  ->
    fun uu___111_150  ->
      match uu___111_150 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____156 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____156 with
           | Some ts -> let uu____160 = subst ts args in Some uu____160
           | uu____161 -> None)
      | uu____163 -> None
let eff_leq:
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____170) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____171 -> false
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___112_176  ->
    match uu___112_176 with
    | FStar_Extraction_ML_Syntax.E_PURE  -> "Pure"
    | FStar_Extraction_ML_Syntax.E_GHOST  -> "Ghost"
    | FStar_Extraction_ML_Syntax.E_IMPURE  -> "Impure"
let join:
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
        | uu____186 ->
            let uu____189 =
              let uu____190 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____190
                (eff_to_string f) (eff_to_string f') in
            failwith uu____189
let join_l:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun uu____210 =
  FStar_List.fold_right
    (fun uu____217  ->
       fun t  ->
         match uu____217 with
         | (uu____221,t0) ->
             FStar_Extraction_ML_Syntax.MLTY_Fun
               (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty option
let rec type_leq_c:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool* FStar_Extraction_ML_Syntax.mlexpr option)
  =
  fun unfold_ty  ->
    fun e  ->
      fun t  ->
        fun t'  ->
          match (t, t') with
          | (FStar_Extraction_ML_Syntax.MLTY_Var
             x,FStar_Extraction_ML_Syntax.MLTY_Var y) ->
              if (fst x) = (fst y) then (true, e) else (false, None)
          | (FStar_Extraction_ML_Syntax.MLTY_Fun
             (t1,f,t2),FStar_Extraction_ML_Syntax.MLTY_Fun (t1',f',t2')) ->
              let mk_fun xs body =
                match xs with
                | [] -> body
                | uu____286 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____304 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____308 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____308 e1 in
              (match e with
               | Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____315;
                     FStar_Extraction_ML_Syntax.loc = uu____316;_}
                   ->
                   let uu____327 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____327
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____337 = type_leq unfold_ty t2 t2' in
                        (if uu____337
                         then
                           let body1 =
                             let uu____345 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____345
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____350 =
                             let uu____352 =
                               let uu____353 =
                                 let uu____356 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____356 in
                               FStar_All.pipe_left uu____353
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             Some uu____352 in
                           (true, uu____350)
                         else (false, None))
                      else
                        (let uu____372 =
                           let uu____376 =
                             let uu____378 = mk_fun xs body in
                             FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                               uu____378 in
                           type_leq_c unfold_ty uu____376 t2 t2' in
                         match uu____372 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | Some body2 ->
                                   let uu____394 = mk_fun [x] body2 in
                                   Some uu____394
                               | uu____399 -> None in
                             (ok, res)))
                   else (false, None)
               | uu____404 ->
                   let uu____406 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____406 then (true, e) else (false, None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____430 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____430 then (true, e) else (false, None))
              else
                (let uu____441 = unfold_ty t in
                 match uu____441 with
                 | Some t1 -> type_leq_c unfold_ty e t1 t'
                 | None  ->
                     let uu____451 = unfold_ty t' in
                     (match uu____451 with
                      | None  -> (false, None)
                      | Some t'1 -> type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____466 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____466 then (true, e) else (false, None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____477,uu____478) ->
              let uu____482 = unfold_ty t in
              (match uu____482 with
               | Some t1 -> type_leq_c unfold_ty e t1 t'
               | uu____492 -> (false, None))
          | (uu____495,FStar_Extraction_ML_Syntax.MLTY_Named uu____496) ->
              let uu____500 = unfold_ty t' in
              (match uu____500 with
               | Some t'1 -> type_leq_c unfold_ty e t t'1
               | uu____510 -> (false, None))
          | uu____513 -> (false, None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____521 = type_leq_c g None t1 t2 in
        FStar_All.pipe_right uu____521 FStar_Pervasives.fst
let is_type_abstraction uu___113_547 =
  match uu___113_547 with
  | (FStar_Util.Inl uu____553,uu____554)::uu____555 -> true
  | uu____567 -> false
let is_xtuple: (Prims.string Prims.list* Prims.string) -> Prims.int option =
  fun uu____579  ->
    match uu____579 with
    | (ns,n1) ->
        if (ns = ["Prims"]) || (ns = ["FStar"; "Pervasives"])
        then
          (match n1 with
           | "Mktuple2" -> Some (Prims.parse_int "2")
           | "Mktuple3" -> Some (Prims.parse_int "3")
           | "Mktuple4" -> Some (Prims.parse_int "4")
           | "Mktuple5" -> Some (Prims.parse_int "5")
           | "Mktuple6" -> Some (Prims.parse_int "6")
           | "Mktuple7" -> Some (Prims.parse_int "7")
           | "Mktuple8" -> Some (Prims.parse_int "8")
           | uu____592 -> None)
        else None
let resugar_exp:
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        (match is_xtuple mlp with
         | Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____602 -> e)
    | uu____604 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___114_609  ->
    match uu___114_609 with
    | f::uu____613 ->
        let uu____615 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____615 with
         | (ns,uu____621) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____628 -> failwith "impos"
let record_fields fs vs =
  FStar_List.map2
    (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e)) fs
    vs
let is_xtuple_ty: (Prims.string Prims.list* Prims.string) -> Prims.int option
  =
  fun uu____662  ->
    match uu____662 with
    | (ns,n1) ->
        if ns = ["FStar"; "Pervasives"]
        then
          (match n1 with
           | "tuple2" -> Some (Prims.parse_int "2")
           | "tuple3" -> Some (Prims.parse_int "3")
           | "tuple4" -> Some (Prims.parse_int "4")
           | "tuple5" -> Some (Prims.parse_int "5")
           | "tuple6" -> Some (Prims.parse_int "6")
           | "tuple7" -> Some (Prims.parse_int "7")
           | "tuple8" -> Some (Prims.parse_int "8")
           | uu____674 -> None)
        else None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        (match is_xtuple_ty mlp with
         | Some n1 -> FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____684 -> t)
    | uu____686 -> t
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____689  ->
    let uu____690 =
      let uu____691 = FStar_Options.codegen () in FStar_Option.get uu____691 in
    uu____690 = "FSharp"
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____698 = codegen_fsharp () in
    if uu____698
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath: (Prims.string Prims.list* Prims.string) -> Prims.string =
  fun uu____705  ->
    match uu____705 with
    | (ns,n1) ->
        let uu____713 = codegen_fsharp () in
        if uu____713
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident -> (Prims.string Prims.list* Prims.string) =
  fun l  ->
    let uu____721 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____721, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____738 = unfold_ty t in
         match uu____738 with
         | Some t1 -> erasableType unfold_ty t1
         | None  -> false)
let rec eraseTypeDeep:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun unfold_ty  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Fun (tyd,etag,tycd) ->
          if etag = FStar_Extraction_ML_Syntax.E_PURE
          then
            let uu____757 =
              let uu____761 = eraseTypeDeep unfold_ty tyd in
              let uu____765 = eraseTypeDeep unfold_ty tycd in
              (uu____761, etag, uu____765) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____757
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____774 = erasableType unfold_ty t in
          if uu____774
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____779 =
               let uu____783 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____783, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____779)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____791 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____791
      | uu____796 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____798 =
    let uu____801 =
      (mk_ty_fun ())
        [(("x", (Prims.parse_int "0")),
           FStar_Extraction_ML_Syntax.ml_bool_ty);
        (("y", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____801 in
  FStar_All.pipe_left uu____798
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_AmpAmp"))
let conjoin:
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun e1  ->
    fun e2  ->
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_bool_ty)
        (FStar_Extraction_ML_Syntax.MLE_App (prims_op_amp_amp, [e1; e2]))
let conjoin_opt:
  FStar_Extraction_ML_Syntax.mlexpr option ->
    FStar_Extraction_ML_Syntax.mlexpr option ->
      FStar_Extraction_ML_Syntax.mlexpr option
  =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (None ,None ) -> None
      | (Some x,None ) -> Some x
      | (None ,Some x) -> Some x
      | (Some x,Some y) -> let uu____854 = conjoin x y in Some uu____854
let mlloc_of_range: FStar_Range.range -> (Prims.int* Prims.string) =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____862 = FStar_Range.file_of_range r in (line, uu____862)
let rec argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____869,b) ->
        let uu____871 = argTypes b in a :: uu____871
    | uu____873 -> []
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list*
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____884,b) ->
        let uu____886 = uncurry_mlty_fun b in
        (match uu____886 with | (args,res) -> ((a :: args), res))
    | uu____898 -> ([], t)