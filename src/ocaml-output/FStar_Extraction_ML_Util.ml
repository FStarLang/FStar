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
      | uu____61 ->
          let uu____62 =
            let uu____63 = FStar_Range.string_of_range p in
            let uu____64 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____63 uu____64 in
          failwith uu____62
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
              (fun uu____86  -> match uu____86 with | (y,uu____90) -> y = x)
              subst1 in
          (match uu____80 with | Some ts -> snd ts | None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____101 =
            let uu____105 = subst_aux subst1 t1 in
            let uu____106 = subst_aux subst1 t2 in (uu____105, f, uu____106) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____101
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____111 =
            let uu____115 = FStar_List.map (subst_aux subst1) args in
            (uu____115, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____111
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____120 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____120
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____129  ->
    fun args  ->
      match uu____129 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then
            failwith
              "Substitution must be fully applied (see GitHub issue #490)"
          else
            (let uu____143 = FStar_List.zip formals args in
             subst_aux uu____143 t)
let udelta_unfold:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty option
  =
  fun g  ->
    fun uu___112_155  ->
      match uu___112_155 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____161 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____161 with
           | Some ts -> let uu____165 = subst ts args in Some uu____165
           | uu____166 -> None)
      | uu____168 -> None
let eff_leq:
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____177) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____178 -> false
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___113_184  ->
    match uu___113_184 with
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
        | uu____197 ->
            let uu____200 =
              let uu____201 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____201
                (eff_to_string f) (eff_to_string f') in
            failwith uu____200
let join_l:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun uu____226 =
  FStar_List.fold_right
    (fun uu____229  ->
       fun t  ->
         match uu____229 with
         | (uu____233,t0) ->
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
                | uu____301 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____319 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____323 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____323 e1 in
              (match e with
               | Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____330;
                     FStar_Extraction_ML_Syntax.loc = uu____331;_}
                   ->
                   let uu____342 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____342
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____352 = type_leq unfold_ty t2 t2' in
                        (if uu____352
                         then
                           let body1 =
                             let uu____360 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____360
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____365 =
                             let uu____367 =
                               let uu____368 =
                                 let uu____371 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____371 in
                               FStar_All.pipe_left uu____368
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             Some uu____367 in
                           (true, uu____365)
                         else (false, None))
                      else
                        (let uu____387 =
                           let uu____391 =
                             let uu____393 = mk_fun xs body in
                             FStar_All.pipe_left (fun _0_40  -> Some _0_40)
                               uu____393 in
                           type_leq_c unfold_ty uu____391 t2 t2' in
                         match uu____387 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | Some body2 ->
                                   let uu____409 = mk_fun [x] body2 in
                                   Some uu____409
                               | uu____414 -> None in
                             (ok, res)))
                   else (false, None)
               | uu____419 ->
                   let uu____421 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____421 then (true, e) else (false, None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____445 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____445 then (true, e) else (false, None))
              else
                (let uu____456 = unfold_ty t in
                 match uu____456 with
                 | Some t1 -> type_leq_c unfold_ty e t1 t'
                 | None  ->
                     let uu____466 = unfold_ty t' in
                     (match uu____466 with
                      | None  -> (false, None)
                      | Some t'1 -> type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____481 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____481 then (true, e) else (false, None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____492,uu____493) ->
              let uu____497 = unfold_ty t in
              (match uu____497 with
               | Some t1 -> type_leq_c unfold_ty e t1 t'
               | uu____507 -> (false, None))
          | (uu____510,FStar_Extraction_ML_Syntax.MLTY_Named uu____511) ->
              let uu____515 = unfold_ty t' in
              (match uu____515 with
               | Some t'1 -> type_leq_c unfold_ty e t t'1
               | uu____525 -> (false, None))
          | uu____528 -> (false, None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____536 = type_leq_c g None t1 t2 in
        FStar_All.pipe_right uu____536 FStar_Pervasives.fst
let is_type_abstraction uu___114_566 =
  match uu___114_566 with
  | (FStar_Util.Inl uu____572,uu____573)::uu____574 -> true
  | uu____586 -> false
let is_xtuple: (Prims.string Prims.list* Prims.string) -> Prims.int option =
  fun uu____599  ->
    match uu____599 with
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
           | uu____612 -> None)
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
         | uu____623 -> e)
    | uu____625 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___115_631  ->
    match uu___115_631 with
    | f::uu____635 ->
        let uu____637 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____637 with
         | (ns,uu____643) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____649 -> failwith "impos"
let record_fields fs vs =
  FStar_List.map2
    (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e)) fs
    vs
let is_xtuple_ty: (Prims.string Prims.list* Prims.string) -> Prims.int option
  =
  fun uu____685  ->
    match uu____685 with
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
           | uu____697 -> None)
        else None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        (match is_xtuple_ty mlp with
         | Some n1 -> FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____708 -> t)
    | uu____710 -> t
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____714  ->
    let uu____715 =
      let uu____716 = FStar_Options.codegen () in FStar_Option.get uu____716 in
    uu____715 = "FSharp"
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____724 = codegen_fsharp () in
    if uu____724
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath: (Prims.string Prims.list* Prims.string) -> Prims.string =
  fun uu____732  ->
    match uu____732 with
    | (ns,n1) ->
        let uu____740 = codegen_fsharp () in
        if uu____740
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident -> (Prims.string Prims.list* Prims.string) =
  fun l  ->
    let uu____749 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____749, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____767 = unfold_ty t in
         match uu____767 with
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
            let uu____788 =
              let uu____792 = eraseTypeDeep unfold_ty tyd in
              let uu____796 = eraseTypeDeep unfold_ty tycd in
              (uu____792, etag, uu____796) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____788
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____805 = erasableType unfold_ty t in
          if uu____805
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____810 =
               let uu____814 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____814, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____810)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____822 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____822
      | uu____827 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____829 =
    let uu____832 =
      (mk_ty_fun ())
        [(("x", (Prims.parse_int "0")),
           FStar_Extraction_ML_Syntax.ml_bool_ty);
        (("y", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____832 in
  FStar_All.pipe_left uu____829
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
      | (Some x,Some y) -> let uu____889 = conjoin x y in Some uu____889
let mlloc_of_range: FStar_Range.range -> (Prims.int* Prims.string) =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____898 = FStar_Range.file_of_range r in (line, uu____898)
let rec argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____907,b) ->
        let uu____909 = argTypes b in a :: uu____909
    | uu____911 -> []
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list*
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____923,b) ->
        let uu____925 = uncurry_mlty_fun b in
        (match uu____925 with | (args,res) -> ((a :: args), res))
    | uu____937 -> ([], t)
type emb_decl =
  | Embed
  | Unembed
let uu___is_Embed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____943 -> false
let uu___is_Unembed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____948 -> false
let lid_to_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun l  ->
    let uu____953 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
    FStar_Extraction_ML_Syntax.MLE_Name uu____953
let lid_to_top_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun l  ->
    let uu____958 =
      let uu____959 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
      FStar_Extraction_ML_Syntax.MLE_Name uu____959 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____958
let str_to_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> let uu____964 = FStar_Ident.lid_of_str s in lid_to_name uu____964
let str_to_top_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr =
  fun s  ->
    let uu____969 = FStar_Ident.lid_of_str s in lid_to_top_name uu____969
let fstar_tc_common_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_TypeChecker_Common." s)
let fstar_refl_basic_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Basic." s)
let mk_embedding:
  emb_decl -> Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun m  ->
    fun s  ->
      match m with
      | Embed  -> fstar_refl_basic_prefix (Prims.strcat "embed_" s)
      | Unembed  -> fstar_refl_basic_prefix (Prims.strcat "unembed_" s)
let rec mk_tac_param_type:
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun t  ->
    let uu____990 =
      let uu____991 = FStar_Syntax_Subst.compress t in
      uu____991.FStar_Syntax_Syntax.n in
    match uu____990 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
        fstar_tc_common_prefix "t_unit"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.string_lid ->
        fstar_tc_common_prefix "t_string"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____997 = FStar_Reflection_Data.fstar_refl_types_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____997 ->
        fstar_tc_common_prefix "t_binder"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____999 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____999 ->
        fstar_tc_common_prefix "t_term"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1001 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1001 ->
        fstar_tc_common_prefix "t_fv"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1003 = FStar_Reflection_Data.fstar_refl_syntax_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1003 ->
        fstar_tc_common_prefix "t_binders"
    | FStar_Syntax_Syntax.Tm_app (h,args) ->
        let uu____1020 =
          let uu____1021 = FStar_Syntax_Subst.compress h in
          uu____1021.FStar_Syntax_Syntax.n in
        (match uu____1020 with
         | FStar_Syntax_Syntax.Tm_uinst (h',uu____1025) ->
             let uu____1030 =
               let uu____1031 = FStar_Syntax_Subst.compress h' in
               uu____1031.FStar_Syntax_Syntax.n in
             (match uu____1030 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Syntax_Const.list_lid
                  ->
                  let arg_term =
                    let uu____1038 = FStar_List.hd args in fst uu____1038 in
                  let uu____1049 =
                    let uu____1053 =
                      let uu____1054 = fstar_tc_common_prefix "t_list_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1054 in
                    let uu____1055 =
                      let uu____1057 =
                        let uu____1059 = mk_tac_param_type arg_term in
                        [uu____1059] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1057 in
                    (uu____1053, uu____1055) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1049
              | uu____1061 ->
                  let uu____1062 =
                    let uu____1063 =
                      let uu____1064 = FStar_Syntax_Subst.compress h' in
                      FStar_Syntax_Print.term_to_string uu____1064 in
                    Prims.strcat
                      "Type term not defined for higher-order type "
                      uu____1063 in
                  failwith uu____1062)
         | uu____1065 -> failwith "Impossible")
    | uu____1066 ->
        let uu____1067 =
          let uu____1068 =
            let uu____1069 = FStar_Syntax_Subst.compress t in
            FStar_Syntax_Print.term_to_string uu____1069 in
          Prims.strcat "Type term not defined for " uu____1068 in
        failwith uu____1067
let rec mk_tac_embedding_path:
  emb_decl -> FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun m  ->
    fun t  ->
      let uu____1078 =
        let uu____1079 = FStar_Syntax_Subst.compress t in
        uu____1079.FStar_Syntax_Syntax.n in
      match uu____1078 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
          mk_embedding m "unit"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.string_lid ->
          mk_embedding m "string"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1085 =
            FStar_Reflection_Data.fstar_refl_types_lid "binder" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1085 ->
          mk_embedding m "binder"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1087 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1087 ->
          mk_embedding m "term"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1089 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1089 ->
          mk_embedding m "fvar"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1091 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "binders" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1091 ->
          mk_embedding m "binders"
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____1108 =
            let uu____1109 = FStar_Syntax_Subst.compress h in
            uu____1109.FStar_Syntax_Syntax.n in
          (match uu____1108 with
           | FStar_Syntax_Syntax.Tm_uinst (h',uu____1113) ->
               let uu____1118 =
                 let uu____1123 =
                   let uu____1124 = FStar_Syntax_Subst.compress h' in
                   uu____1124.FStar_Syntax_Syntax.n in
                 match uu____1123 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.list_lid
                     ->
                     let arg_term =
                       let uu____1135 = FStar_List.hd args in fst uu____1135 in
                     let uu____1146 =
                       let uu____1148 = mk_tac_embedding_path m arg_term in
                       [uu____1148] in
                     let uu____1149 = mk_tac_param_type arg_term in
                     ("list", uu____1146, uu____1149)
                 | uu____1151 ->
                     let uu____1152 =
                       let uu____1153 =
                         let uu____1154 = FStar_Syntax_Subst.compress h' in
                         FStar_Syntax_Print.term_to_string uu____1154 in
                       Prims.strcat
                         "Embedding not defined for higher-order type "
                         uu____1153 in
                     failwith uu____1152 in
               (match uu____1118 with
                | (ht,hargs,type_arg) ->
                    let hargs1 =
                      match m with
                      | Embed  -> FStar_List.append hargs [type_arg]
                      | Unembed  -> hargs in
                    let uu____1167 =
                      let uu____1171 =
                        let uu____1172 = mk_embedding m ht in
                        FStar_Extraction_ML_Syntax.with_ty
                          FStar_Extraction_ML_Syntax.MLTY_Top uu____1172 in
                      let uu____1173 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) hargs1 in
                      (uu____1171, uu____1173) in
                    FStar_Extraction_ML_Syntax.MLE_App uu____1167)
           | uu____1176 -> failwith "Impossible")
      | uu____1177 ->
          let uu____1178 =
            let uu____1179 =
              let uu____1180 = FStar_Syntax_Subst.compress t in
              FStar_Syntax_Print.term_to_string uu____1180 in
            Prims.strcat "Embedding not defined for type " uu____1179 in
          failwith uu____1178
let mk_interpretation_fun tac_lid assm_lid t bs =
  let arg_types =
    FStar_List.map (fun x  -> (fst x).FStar_Syntax_Syntax.sort) bs in
  let arity = FStar_List.length bs in
  let h =
    let uu____1231 =
      let uu____1232 = FStar_Util.string_of_int arity in
      Prims.strcat "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
        uu____1232 in
    str_to_top_name uu____1231 in
  let tac_fun =
    let uu____1240 =
      let uu____1244 =
        let uu____1245 =
          let uu____1246 = FStar_Util.string_of_int arity in
          Prims.strcat "FStar_Tactics_Native.from_tactic_" uu____1246 in
        str_to_top_name uu____1245 in
      let uu____1253 =
        let uu____1255 = lid_to_top_name tac_lid in [uu____1255] in
      (uu____1244, uu____1253) in
    FStar_Extraction_ML_Syntax.MLE_App uu____1240 in
  let tac_lid_app =
    let uu____1258 =
      let uu____1262 = str_to_top_name "FStar_Ident.lid_of_str" in
      (uu____1262,
        [FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top assm_lid]) in
    FStar_Extraction_ML_Syntax.MLE_App uu____1258 in
  let args =
    let uu____1266 =
      let uu____1268 = str_to_name "ps" in [uu____1268; tac_fun] in
    let uu____1269 =
      let uu____1271 =
        FStar_List.map (mk_tac_embedding_path Unembed) arg_types in
      let uu____1273 =
        let uu____1275 = mk_tac_embedding_path Embed t in
        let uu____1276 =
          let uu____1278 = mk_tac_param_type t in
          let uu____1279 =
            let uu____1281 =
              let uu____1283 = str_to_name "args" in [uu____1283] in
            tac_lid_app :: uu____1281 in
          uu____1278 :: uu____1279 in
        uu____1275 :: uu____1276 in
      FStar_List.append uu____1271 uu____1273 in
    FStar_List.append uu____1266 uu____1269 in
  let app =
    let uu____1285 =
      let uu____1286 =
        let uu____1290 =
          FStar_List.map
            (FStar_Extraction_ML_Syntax.with_ty
               FStar_Extraction_ML_Syntax.MLTY_Top) args in
        (h, uu____1290) in
      FStar_Extraction_ML_Syntax.MLE_App uu____1286 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1285 in
  FStar_Extraction_ML_Syntax.MLE_Fun
    ([(("ps", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.MLTY_Top);
     (("args", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.MLTY_Top)],
      app)