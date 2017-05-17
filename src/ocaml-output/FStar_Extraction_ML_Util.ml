open Prims
let pruneNones l =
  FStar_List.fold_right
    (fun x  -> fun ll  -> match x with | Some xs -> xs :: ll | None  -> ll) l
    []
let mlconst_of_const:
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
let mlconst_of_const':
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const c
      with
      | uu____56 ->
          let uu____57 =
            let uu____58 = FStar_Range.string_of_range p in
            let uu____59 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____58 uu____59 in
          failwith uu____57
let rec subst_aux:
  (FStar_Extraction_ML_Syntax.mlident* FStar_Extraction_ML_Syntax.mlty)
    Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____73 =
            FStar_Util.find_opt
              (fun uu____79  -> match uu____79 with | (y,uu____83) -> y = x)
              subst1 in
          (match uu____73 with | Some ts -> Prims.snd ts | None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____94 =
            let uu____98 = subst_aux subst1 t1 in
            let uu____99 = subst_aux subst1 t2 in (uu____98, f, uu____99) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____94
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____104 =
            let uu____108 = FStar_List.map (subst_aux subst1) args in
            (uu____108, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____104
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____113 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____113
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let subst:
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
            (let uu____130 = FStar_List.zip formals args in
             subst_aux uu____130 t)
let udelta_unfold:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty Prims.option
  =
  fun g  ->
    fun uu___115_140  ->
      match uu___115_140 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____146 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____146 with
           | Some ts -> let uu____150 = subst ts args in Some uu____150
           | uu____151 -> None)
      | uu____153 -> None
let eff_leq:
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
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___116_166  ->
    match uu___116_166 with
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
        | uu____176 ->
            let uu____179 =
              let uu____180 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____180
                (eff_to_string f) (eff_to_string f') in
            failwith uu____179
let join_l:
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
    FStar_Extraction_ML_Syntax.mlty Prims.option
let rec type_leq_c:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool* FStar_Extraction_ML_Syntax.mlexpr Prims.option)
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
                | uu____275 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____293 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____297 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____297 e1 in
              (match e with
               | Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____304;
                     FStar_Extraction_ML_Syntax.loc = uu____305;_}
                   ->
                   let uu____316 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____316
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____326 = type_leq unfold_ty t2 t2' in
                        (if uu____326
                         then
                           let body1 =
                             let uu____334 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____334
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____339 =
                             let uu____341 =
                               let uu____342 =
                                 let uu____345 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____345 in
                               FStar_All.pipe_left uu____342
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             Some uu____341 in
                           (true, uu____339)
                         else (false, None))
                      else
                        (let uu____361 =
                           let uu____365 =
                             let uu____367 = mk_fun xs body in
                             FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                               uu____367 in
                           type_leq_c unfold_ty uu____365 t2 t2' in
                         match uu____361 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | Some body2 ->
                                   let uu____383 = mk_fun [x] body2 in
                                   Some uu____383
                               | uu____388 -> None in
                             (ok, res)))
                   else (false, None)
               | uu____393 ->
                   let uu____395 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____395 then (true, e) else (false, None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____419 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____419 then (true, e) else (false, None))
              else
                (let uu____430 = unfold_ty t in
                 match uu____430 with
                 | Some t1 -> type_leq_c unfold_ty e t1 t'
                 | None  ->
                     let uu____440 = unfold_ty t' in
                     (match uu____440 with
                      | None  -> (false, None)
                      | Some t'1 -> type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____455 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____455 then (true, e) else (false, None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____466,uu____467) ->
              let uu____471 = unfold_ty t in
              (match uu____471 with
               | Some t1 -> type_leq_c unfold_ty e t1 t'
               | uu____481 -> (false, None))
          | (uu____484,FStar_Extraction_ML_Syntax.MLTY_Named uu____485) ->
              let uu____489 = unfold_ty t' in
              (match uu____489 with
               | Some t'1 -> type_leq_c unfold_ty e t t'1
               | uu____499 -> (false, None))
          | uu____502 -> (false, None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____510 = type_leq_c g None t1 t2 in
        FStar_All.pipe_right uu____510 Prims.fst
let is_type_abstraction uu___117_536 =
  match uu___117_536 with
  | (FStar_Util.Inl uu____542,uu____543)::uu____544 -> true
  | uu____556 -> false
let is_xtuple:
  (Prims.string Prims.list* Prims.string) -> Prims.int Prims.option =
  fun uu____568  ->
    match uu____568 with
    | (ns,n1) ->
        if ns = ["Prims"]
        then
          (match n1 with
           | "Mktuple2" -> Some (Prims.parse_int "2")
           | "Mktuple3" -> Some (Prims.parse_int "3")
           | "Mktuple4" -> Some (Prims.parse_int "4")
           | "Mktuple5" -> Some (Prims.parse_int "5")
           | "Mktuple6" -> Some (Prims.parse_int "6")
           | "Mktuple7" -> Some (Prims.parse_int "7")
           | "Mktuple8" -> Some (Prims.parse_int "8")
           | uu____580 -> None)
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
         | uu____590 -> e)
    | uu____592 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___118_597  ->
    match uu___118_597 with
    | f::uu____601 ->
        let uu____603 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____603 with
         | (ns,uu____609) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____615 -> failwith "impos"
let record_fields fs vs =
  FStar_List.map2
    (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e)) fs
    vs
let is_xtuple_ty:
  (Prims.string Prims.list* Prims.string) -> Prims.int Prims.option =
  fun uu____647  ->
    match uu____647 with
    | (ns,n1) ->
        if ns = ["Prims"]
        then
          (match n1 with
           | "tuple2" -> Some (Prims.parse_int "2")
           | "tuple3" -> Some (Prims.parse_int "3")
           | "tuple4" -> Some (Prims.parse_int "4")
           | "tuple5" -> Some (Prims.parse_int "5")
           | "tuple6" -> Some (Prims.parse_int "6")
           | "tuple7" -> Some (Prims.parse_int "7")
           | "tuple8" -> Some (Prims.parse_int "8")
           | uu____659 -> None)
        else None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        (match is_xtuple_ty mlp with
         | Some n1 -> FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____669 -> t)
    | uu____671 -> t
let codegen_fsharp: Prims.unit -> Prims.bool =
  fun uu____674  ->
    let uu____675 =
      let uu____676 = FStar_Options.codegen () in FStar_Option.get uu____676 in
    uu____675 = "FSharp"
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____683 = codegen_fsharp () in
    if uu____683
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath: (Prims.string Prims.list* Prims.string) -> Prims.string =
  fun uu____690  ->
    match uu____690 with
    | (ns,n1) ->
        let uu____698 = codegen_fsharp () in
        if uu____698
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident -> (Prims.string Prims.list* Prims.string) =
  fun l  ->
    let uu____706 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____706, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____722 = unfold_ty t in
         match uu____722 with
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
            let uu____741 =
              let uu____745 = eraseTypeDeep unfold_ty tyd in
              let uu____749 = eraseTypeDeep unfold_ty tycd in
              (uu____745, etag, uu____749) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____741
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____758 = erasableType unfold_ty t in
          if uu____758
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____763 =
               let uu____767 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____767, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____763)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____775 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____775
      | uu____780 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____782 =
    let uu____785 =
      (mk_ty_fun ())
        [(("x", (Prims.parse_int "0")),
           FStar_Extraction_ML_Syntax.ml_bool_ty);
        (("y", (Prims.parse_int "0")), FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____785 in
  FStar_All.pipe_left uu____782
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
  FStar_Extraction_ML_Syntax.mlexpr Prims.option ->
    FStar_Extraction_ML_Syntax.mlexpr Prims.option ->
      FStar_Extraction_ML_Syntax.mlexpr Prims.option
  =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (None ,None ) -> None
      | (Some x,None )|(None ,Some x) -> Some x
      | (Some x,Some y) -> let uu____837 = conjoin x y in Some uu____837
let mlloc_of_range: FStar_Range.range -> (Prims.int* Prims.string) =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____845 = FStar_Range.file_of_range r in (line, uu____845)
let rec argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____853,b) ->
        let uu____855 = argTypes b in a :: uu____855
    | uu____857 -> []
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list*
      FStar_Extraction_ML_Syntax.mlty)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____868,b) ->
        let uu____870 = uncurry_mlty_fun b in
        (match uu____870 with | (args,res) -> ((a :: args), res))
    | uu____882 -> ([], t)