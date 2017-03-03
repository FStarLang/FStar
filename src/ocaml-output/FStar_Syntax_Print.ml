open Prims
let sli: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____4 = FStar_Options.print_real_names () in
    if uu____4
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let lid_to_string: FStar_Ident.lid -> Prims.string = fun l  -> sli l
let fv_to_string: FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let bv_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let _0_312 =
      let _0_311 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" _0_311 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText _0_312
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____22 = FStar_Options.print_real_names () in
    if uu____22
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let _0_314 =
      let _0_313 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" _0_313 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText _0_314
let infix_prim_ops: (FStar_Ident.lident* Prims.string) Prims.list =
  [(FStar_Syntax_Const.op_Addition, "+");
  (FStar_Syntax_Const.op_Subtraction, "-");
  (FStar_Syntax_Const.op_Multiply, "*");
  (FStar_Syntax_Const.op_Division, "/");
  (FStar_Syntax_Const.op_Eq, "=");
  (FStar_Syntax_Const.op_ColonEq, ":=");
  (FStar_Syntax_Const.op_notEq, "<>");
  (FStar_Syntax_Const.op_And, "&&");
  (FStar_Syntax_Const.op_Or, "||");
  (FStar_Syntax_Const.op_LTE, "<=");
  (FStar_Syntax_Const.op_GTE, ">=");
  (FStar_Syntax_Const.op_LT, "<");
  (FStar_Syntax_Const.op_GT, ">");
  (FStar_Syntax_Const.op_Modulus, "mod");
  (FStar_Syntax_Const.and_lid, "/\\");
  (FStar_Syntax_Const.or_lid, "\\/");
  (FStar_Syntax_Const.imp_lid, "==>");
  (FStar_Syntax_Const.iff_lid, "<==>");
  (FStar_Syntax_Const.precedes_lid, "<<");
  (FStar_Syntax_Const.eq2_lid, "==");
  (FStar_Syntax_Const.eq3_lid, "===")]
let unary_prim_ops: (FStar_Ident.lident* Prims.string) Prims.list =
  [(FStar_Syntax_Const.op_Negation, "not");
  (FStar_Syntax_Const.op_Minus, "-");
  (FStar_Syntax_Const.not_lid, "~")]
let is_prim_op ps f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_All.pipe_right ps
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
  | uu____105 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____122 -> failwith "get_lid"
let is_infix_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (Prims.fst (FStar_List.split infix_prim_ops)) e
let is_unary_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (Prims.fst (FStar_List.split unary_prim_ops)) e
let quants: (FStar_Ident.lident* Prims.string) Prims.list =
  [(FStar_Syntax_Const.forall_lid, "forall");
  (FStar_Syntax_Const.exists_lid, "exists")]
type exp = FStar_Syntax_Syntax.term
let is_b2t: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.b2t_lid] t
let is_quant: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op (Prims.fst (FStar_List.split quants)) t
let is_ite: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.ite_lid] t
let is_lex_cons: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Syntax_Const.lexcons_lid] f
let is_lex_top: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Syntax_Const.lextop_lid] f
let is_inr uu___180_169 =
  match uu___180_169 with
  | FStar_Util.Inl uu____172 -> false
  | FStar_Util.Inr uu____173 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___181_204  ->
          match uu___181_204 with
          | (uu____208,Some (FStar_Syntax_Syntax.Implicit uu____209)) ->
              false
          | uu____211 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list Prims.option
  =
  fun e  ->
    let uu____222 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n in
    match uu____222 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args = filter_imp args in
        let exps = FStar_List.map Prims.fst args in
        let uu____266 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____266
        then
          let uu____275 =
            reconstruct_lex (FStar_List.nth exps (Prims.parse_int "1")) in
          (match uu____275 with
           | Some xs ->
               Some
                 (let _0_315 = FStar_List.nth exps (Prims.parse_int "0") in
                  _0_315 :: xs)
           | None  -> None)
        else None
    | uu____310 ->
        let uu____311 = is_lex_top e in if uu____311 then Some [] else None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd::tl -> let uu____347 = f hd in if uu____347 then hd else find f tl
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident* Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      Prims.snd (find (fun p  -> FStar_Ident.lid_equals x (Prims.fst p)) xs)
let infix_prim_op_to_string e =
  let _0_316 = get_lid e in find_lid _0_316 infix_prim_ops
let unary_prim_op_to_string e =
  let _0_317 = get_lid e in find_lid _0_317 unary_prim_ops
let quant_to_string t = let _0_318 = get_lid t in find_lid _0_318 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x -> FStar_Util.string_of_float x
    | FStar_Const.Const_string (bytes,uu____406) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____409 -> "<bytearray>"
    | FStar_Const.Const_int (x,uu____414) -> x
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let _0_319 = sli l in FStar_Util.format1 "[[%s.reflect]]" _0_319
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___182_426  ->
    match uu___182_426 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let _0_320 = db_to_string x in Prims.strcat "Tm_bvar: " _0_320
    | FStar_Syntax_Syntax.Tm_name x ->
        let _0_321 = nm_to_string x in Prims.strcat "Tm_name: " _0_321
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let _0_322 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " _0_322
    | FStar_Syntax_Syntax.Tm_uinst uu____443 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____448 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____449 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____450 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____465 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____473 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____478 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____488 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____504 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____517 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____525 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____534,m) ->
        let uu____572 = FStar_ST.read m in
        (match uu____572 with
         | None  -> "Tm_delayed"
         | Some uu____583 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____588 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string u =
  let uu____602 = FStar_Options.hide_uvar_nums () in
  if uu____602
  then "?"
  else
    (let _0_324 =
       let _0_323 = FStar_Unionfind.uvar_id u in
       FStar_All.pipe_right _0_323 FStar_Util.string_of_int in
     Prims.strcat "?" _0_324)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe Prims.option)
  =
  fun n  ->
    fun u  ->
      let uu____613 = FStar_Syntax_Subst.compress_univ u in
      match uu____613 with
      | FStar_Syntax_Syntax.U_zero  -> (n, None)
      | FStar_Syntax_Syntax.U_succ u ->
          int_of_univ (n + (Prims.parse_int "1")) u
      | uu____619 -> (n, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____624 = FStar_Syntax_Subst.compress_univ u in
    match uu____624 with
    | FStar_Syntax_Syntax.U_unif u -> uvar_to_string u
    | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let _0_325 = FStar_Util.string_of_int x in Prims.strcat "@" _0_325
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u ->
        let uu____632 = int_of_univ (Prims.parse_int "1") u in
        (match uu____632 with
         | (n,None ) -> FStar_Util.string_of_int n
         | (n,Some u) ->
             let _0_327 = univ_to_string u in
             let _0_326 = FStar_Util.string_of_int n in
             FStar_Util.format2 "(%s + %s)" _0_327 _0_326)
    | FStar_Syntax_Syntax.U_max us ->
        let _0_329 =
          let _0_328 = FStar_List.map univ_to_string us in
          FStar_All.pipe_right _0_328 (FStar_String.concat ", ") in
        FStar_Util.format1 "(max %s)" _0_329
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let _0_330 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right _0_330 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let _0_331 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right _0_331 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___183_659  ->
    match uu___183_659 with
    | FStar_Syntax_Syntax.Assumption  -> "assume"
    | FStar_Syntax_Syntax.New  -> "new"
    | FStar_Syntax_Syntax.Private  -> "private"
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> "unfold"
    | FStar_Syntax_Syntax.Inline_for_extraction  -> "inline"
    | FStar_Syntax_Syntax.NoExtract  -> "noextract"
    | FStar_Syntax_Syntax.Visible_default  -> "visible"
    | FStar_Syntax_Syntax.Irreducible  -> "irreducible"
    | FStar_Syntax_Syntax.Abstract  -> "abstract"
    | FStar_Syntax_Syntax.Noeq  -> "noeq"
    | FStar_Syntax_Syntax.Unopteq  -> "unopteq"
    | FStar_Syntax_Syntax.Logic  -> "logic"
    | FStar_Syntax_Syntax.TotalEffect  -> "total"
    | FStar_Syntax_Syntax.Discriminator l ->
        let _0_332 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" _0_332
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let _0_333 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" _0_333 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let _0_336 = FStar_Ident.text_of_path (FStar_Ident.path_of_ns ns) in
        let _0_335 =
          let _0_334 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right _0_334 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" _0_336 _0_335
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let _0_339 = FStar_Ident.text_of_path (FStar_Ident.path_of_ns ns) in
        let _0_338 =
          let _0_337 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right _0_337 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" _0_339 _0_338
    | FStar_Syntax_Syntax.Action eff_lid ->
        let _0_340 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" _0_340
    | FStar_Syntax_Syntax.ExceptionConstructor  -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect  -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect  -> "Effect"
    | FStar_Syntax_Syntax.Reifiable  -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str
    | FStar_Syntax_Syntax.OnlyName  -> "OnlyName"
let quals_to_string: FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string
  =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____688 ->
        let _0_341 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right _0_341 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____698 ->
        let _0_342 = quals_to_string quals in Prims.strcat _0_342 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let x = FStar_Syntax_Subst.compress x in
    let x =
      let uu____755 = FStar_Options.print_implicits () in
      if uu____755 then x else FStar_Syntax_Util.unmeta x in
    match x.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____757 -> failwith "impossible"
    | FStar_Syntax_Syntax.Tm_app (uu____778,[]) -> failwith "Empty args!"
    | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps) ->
        let pats =
          let _0_344 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let _0_343 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____827  ->
                              match uu____827 with
                              | (t,uu____831) -> term_to_string t)) in
                    FStar_All.pipe_right _0_343 (FStar_String.concat "; "))) in
          FStar_All.pipe_right _0_344 (FStar_String.concat "\\/") in
        let _0_345 = term_to_string t in
        FStar_Util.format2 "{:pattern %s} %s" pats _0_345
    | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_monadic (m,t'))
        ->
        let _0_349 = tag_of_term t in
        let _0_348 = sli m in
        let _0_347 = term_to_string t' in
        let _0_346 = term_to_string t in
        FStar_Util.format4 "(Monadic-%s{%s %s} %s)" _0_349 _0_348 _0_347
          _0_346
    | FStar_Syntax_Syntax.Tm_meta
        (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
        let _0_354 = tag_of_term t in
        let _0_353 = term_to_string t' in
        let _0_352 = sli m0 in
        let _0_351 = sli m1 in
        let _0_350 = term_to_string t in
        FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" _0_354 _0_353
          _0_352 _0_351 _0_350
    | FStar_Syntax_Syntax.Tm_meta
        (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
        FStar_Options.print_implicits () ->
        let _0_356 = FStar_Range.string_of_range r in
        let _0_355 = term_to_string t in
        FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l _0_356 _0_355
    | FStar_Syntax_Syntax.Tm_meta (t,uu____864) -> term_to_string t
    | FStar_Syntax_Syntax.Tm_bvar x -> db_to_string x
    | FStar_Syntax_Syntax.Tm_name x -> nm_to_string x
    | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____873) -> uvar_to_string u
    | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
    | FStar_Syntax_Syntax.Tm_type u ->
        let uu____891 = FStar_Options.print_universes () in
        if uu____891
        then
          let _0_357 = univ_to_string u in
          FStar_Util.format1 "Type(%s)" _0_357
        else "Type"
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let _0_359 = binders_to_string " -> " bs in
        let _0_358 = comp_to_string c in
        FStar_Util.format2 "(%s -> %s)" _0_359 _0_358
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
        (match lc with
         | Some (FStar_Util.Inl l) when FStar_Options.print_implicits () ->
             let _0_363 = binders_to_string " " bs in
             let _0_362 = term_to_string t2 in
             let _0_361 =
               let _0_360 = l.FStar_Syntax_Syntax.comp () in
               FStar_All.pipe_left comp_to_string _0_360 in
             FStar_Util.format3 "(fun %s -> (%s $$ %s))" _0_363 _0_362 _0_361
         | Some (FStar_Util.Inr (l,flags)) when
             FStar_Options.print_implicits () ->
             let _0_365 = binders_to_string " " bs in
             let _0_364 = term_to_string t2 in
             FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))" _0_365
               _0_364 l.FStar_Ident.str
         | uu____951 ->
             let _0_367 = binders_to_string " " bs in
             let _0_366 = term_to_string t2 in
             FStar_Util.format2 "(fun %s -> %s)" _0_367 _0_366)
    | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
        let _0_370 = bv_to_string xt in
        let _0_369 =
          FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
        let _0_368 = FStar_All.pipe_right f formula_to_string in
        FStar_Util.format3 "(%s:%s{%s})" _0_370 _0_369 _0_368
    | FStar_Syntax_Syntax.Tm_app (t,args) ->
        let _0_372 = term_to_string t in
        let _0_371 = args_to_string args in
        FStar_Util.format2 "(%s %s)" _0_372 _0_371
    | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
        let _0_374 = lbs_to_string [] lbs in
        let _0_373 = term_to_string e in
        FStar_Util.format2 "%s\nin\n%s" _0_374 _0_373
    | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t,eff_name) ->
        let _0_378 = term_to_string e in
        let _0_377 =
          let _0_375 = FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
          FStar_All.pipe_right _0_375 (FStar_Util.dflt "default") in
        let _0_376 = term_to_string t in
        FStar_Util.format3 "(%s <: [%s] %s)" _0_378 _0_377 _0_376
    | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inr c,uu____1020) ->
        let _0_380 = term_to_string e in
        let _0_379 = comp_to_string c in
        FStar_Util.format2 "(%s <: %s)" _0_380 _0_379
    | FStar_Syntax_Syntax.Tm_match (head,branches) ->
        let _0_387 = term_to_string head in
        let _0_386 =
          let _0_385 =
            FStar_All.pipe_right branches
              (FStar_List.map
                 (fun uu____1083  ->
                    match uu____1083 with
                    | (p,wopt,e) ->
                        let _0_384 = FStar_All.pipe_right p pat_to_string in
                        let _0_383 =
                          match wopt with
                          | None  -> ""
                          | Some w ->
                              let _0_381 =
                                FStar_All.pipe_right w term_to_string in
                              FStar_Util.format1 "when %s" _0_381 in
                        let _0_382 = FStar_All.pipe_right e term_to_string in
                        FStar_Util.format3 "%s %s -> %s" _0_384 _0_383 _0_382)) in
          FStar_Util.concat_l "\n\t|" _0_385 in
        FStar_Util.format2 "(match %s with\n\t| %s)" _0_387 _0_386
    | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
        let uu____1100 = FStar_Options.print_universes () in
        if uu____1100
        then
          let _0_389 = term_to_string t in
          let _0_388 = univs_to_string us in
          FStar_Util.format2 "%s<%s>" _0_389 _0_388
        else term_to_string t
    | uu____1102 -> tag_of_term x
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
        let _0_392 = fv_to_string l in
        let _0_391 =
          let _0_390 =
            FStar_List.map
              (fun uu____1119  ->
                 match uu____1119 with
                 | (x,b) ->
                     let p = pat_to_string x in
                     if b then Prims.strcat "#" p else p) pats in
          FStar_All.pipe_right _0_390 (FStar_String.concat " ") in
        FStar_Util.format2 "(%s %s)" _0_392 _0_391
    | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1127) ->
        let uu____1132 = FStar_Options.print_bound_var_types () in
        if uu____1132
        then
          let _0_394 = bv_to_string x in
          let _0_393 = term_to_string x.FStar_Syntax_Syntax.sort in
          FStar_Util.format2 ".%s:%s" _0_394 _0_393
        else (let _0_395 = bv_to_string x in FStar_Util.format1 ".%s" _0_395)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____1135 = FStar_Options.print_bound_var_types () in
        if uu____1135
        then
          let _0_397 = bv_to_string x in
          let _0_396 = term_to_string x.FStar_Syntax_Syntax.sort in
          FStar_Util.format2 "%s:%s" _0_397 _0_396
        else bv_to_string x
    | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____1139 = FStar_Options.print_real_names () in
        if uu____1139
        then let _0_398 = bv_to_string x in Prims.strcat "Pat_wild " _0_398
        else "_"
    | FStar_Syntax_Syntax.Pat_disj ps ->
        let _0_399 = FStar_List.map pat_to_string ps in
        FStar_Util.concat_l " | " _0_399
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs =
        let uu____1155 = FStar_Options.print_universes () in
        if uu____1155
        then
          let _0_401 =
            FStar_All.pipe_right (Prims.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1165 =
                      let _0_400 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs _0_400 in
                    match uu____1165 with
                    | (us,td) ->
                        let uu____1170 =
                          let uu____1177 =
                            (FStar_Syntax_Subst.compress td).FStar_Syntax_Syntax.n in
                          match uu____1177 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1184,(t,uu____1186)::(d,uu____1188)::[])
                              -> (t, d)
                          | uu____1222 -> failwith "Impossibe" in
                        (match uu____1170 with
                         | (t,d) ->
                             let uu___190_1239 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___190_1239.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___190_1239.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((Prims.fst lbs), _0_401)
        else lbs in
      let _0_410 = quals_to_string' quals in
      let _0_409 =
        let _0_408 =
          FStar_All.pipe_right (Prims.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let _0_407 = lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let _0_406 =
                    let uu____1247 = FStar_Options.print_universes () in
                    if uu____1247
                    then
                      let _0_403 =
                        let _0_402 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat _0_402 ">" in
                      Prims.strcat "<" _0_403
                    else "" in
                  let _0_405 = term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let _0_404 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" _0_407 _0_406 _0_405
                    _0_404)) in
        FStar_Util.concat_l "\n and " _0_408 in
      FStar_Util.format3 "%slet %s %s" _0_410
        (if Prims.fst lbs then "rec" else "") _0_409
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1252 = FStar_Options.print_effect_args () in
    if uu____1252
    then comp_to_string (lc.FStar_Syntax_Syntax.comp ())
    else
      (let _0_412 = sli lc.FStar_Syntax_Syntax.eff_name in
       let _0_411 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" _0_412 _0_411)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.string
  =
  fun s  ->
    fun uu___184_1255  ->
      match uu___184_1255 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1257 -> s
and binder_to_string':
  Prims.bool ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) -> Prims.string
  =
  fun is_arrow  ->
    fun b  ->
      let uu____1263 = b in
      match uu____1263 with
      | (a,imp) ->
          let uu____1268 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____1268
          then
            let _0_413 = term_to_string a.FStar_Syntax_Syntax.sort in
            Prims.strcat "_:" _0_413
          else
            (let uu____1270 =
               (Prims.op_Negation is_arrow) &&
                 (Prims.op_Negation (FStar_Options.print_bound_var_types ())) in
             if uu____1270
             then let _0_414 = nm_to_string a in imp_to_string _0_414 imp
             else
               (let _0_418 =
                  let _0_417 = nm_to_string a in
                  let _0_416 =
                    let _0_415 = term_to_string a.FStar_Syntax_Syntax.sort in
                    Prims.strcat ":" _0_415 in
                  Prims.strcat _0_417 _0_416 in
                imp_to_string _0_418 imp))
and binder_to_string:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs =
        let uu____1281 = FStar_Options.print_implicits () in
        if uu____1281 then bs else filter_imp bs in
      if sep = " -> "
      then
        let _0_419 =
          FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right _0_419 (FStar_String.concat sep)
      else
        (let _0_420 =
           FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
         FStar_All.pipe_right _0_420 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier Prims.option)
    -> Prims.string
  =
  fun uu___185_1292  ->
    match uu___185_1292 with
    | (a,imp) -> let _0_421 = term_to_string a in imp_to_string _0_421 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args =
      let uu____1302 = FStar_Options.print_implicits () in
      if uu____1302 then args else filter_imp args in
    let _0_422 = FStar_All.pipe_right args (FStar_List.map arg_to_string) in
    FStar_All.pipe_right _0_422 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1313) ->
        let uu____1320 =
          (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
        (match uu____1320 with
         | FStar_Syntax_Syntax.Tm_type uu____1321 when
             Prims.op_Negation (FStar_Options.print_implicits ()) ->
             term_to_string t
         | uu____1322 ->
             let _0_423 = term_to_string t in
             FStar_Util.format1 "Tot %s" _0_423)
    | FStar_Syntax_Syntax.GTotal (t,uu____1324) ->
        let uu____1331 =
          (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
        (match uu____1331 with
         | FStar_Syntax_Syntax.Tm_type uu____1332 when
             Prims.op_Negation (FStar_Options.print_implicits ()) ->
             term_to_string t
         | uu____1333 ->
             let _0_424 = term_to_string t in
             FStar_Util.format1 "GTot %s" _0_424)
    | FStar_Syntax_Syntax.Comp c ->
        let basic =
          let uu____1336 = FStar_Options.print_effect_args () in
          if uu____1336
          then
            let _0_430 = sli c.FStar_Syntax_Syntax.effect_name in
            let _0_429 = term_to_string c.FStar_Syntax_Syntax.result_typ in
            let _0_428 =
              let _0_425 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map arg_to_string) in
              FStar_All.pipe_right _0_425 (FStar_String.concat ", ") in
            let _0_427 =
              let _0_426 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                  (FStar_List.map cflags_to_string) in
              FStar_All.pipe_right _0_426 (FStar_String.concat " ") in
            FStar_Util.format4 "%s (%s) %s (attributes %s)" _0_430 _0_429
              _0_428 _0_427
          else
            (let uu____1351 =
               (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___186_1353  ->
                        match uu___186_1353 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____1354 -> false)))
                 && (Prims.op_Negation (FStar_Options.print_effect_args ())) in
             if uu____1351
             then
               let _0_431 = term_to_string c.FStar_Syntax_Syntax.result_typ in
               FStar_Util.format1 "Tot %s" _0_431
             else
               (let uu____1356 =
                  ((Prims.op_Negation (FStar_Options.print_effect_args ()))
                     &&
                     (Prims.op_Negation (FStar_Options.print_implicits ())))
                    &&
                    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name
                       FStar_Syntax_Const.effect_ML_lid) in
                if uu____1356
                then term_to_string c.FStar_Syntax_Syntax.result_typ
                else
                  (let uu____1358 =
                     (Prims.op_Negation (FStar_Options.print_effect_args ()))
                       &&
                       (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                          (FStar_Util.for_some
                             (fun uu___187_1360  ->
                                match uu___187_1360 with
                                | FStar_Syntax_Syntax.MLEFFECT  -> true
                                | uu____1361 -> false))) in
                   if uu____1358
                   then
                     let _0_432 =
                       term_to_string c.FStar_Syntax_Syntax.result_typ in
                     FStar_Util.format1 "ALL %s" _0_432
                   else
                     (let _0_434 = sli c.FStar_Syntax_Syntax.effect_name in
                      let _0_433 =
                        term_to_string c.FStar_Syntax_Syntax.result_typ in
                      FStar_Util.format2 "%s (%s)" _0_434 _0_433)))) in
        let dec =
          let _0_437 =
            FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
              (FStar_List.collect
                 (fun uu___188_1367  ->
                    match uu___188_1367 with
                    | FStar_Syntax_Syntax.DECREASES e ->
                        let _0_436 =
                          let _0_435 = term_to_string e in
                          FStar_Util.format1 " (decreases %s)" _0_435 in
                        [_0_436]
                    | uu____1372 -> [])) in
          FStar_All.pipe_right _0_437 (FStar_String.concat " ") in
        FStar_Util.format2 "%s%s" basic dec
and cflags_to_string: FStar_Syntax_Syntax.cflags -> Prims.string =
  fun c  ->
    match c with
    | FStar_Syntax_Syntax.TOTAL  -> "total"
    | FStar_Syntax_Syntax.MLEFFECT  -> "ml"
    | FStar_Syntax_Syntax.RETURN  -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN  -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL  -> "sometrivial"
    | FStar_Syntax_Syntax.LEMMA  -> "lemma"
    | FStar_Syntax_Syntax.CPS  -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____1374 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1383 = FStar_Options.print_universes () in
    if uu____1383 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun uu____1387  ->
    match uu____1387 with
    | (us,t) ->
        let _0_440 =
          let _0_438 = univ_names_to_string us in
          FStar_All.pipe_left enclose_universes _0_438 in
        let _0_439 = term_to_string t in
        FStar_Util.format2 "%s%s" _0_440 _0_439
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  ->
      let actions_to_string actions =
        let _0_446 =
          FStar_All.pipe_right actions
            (FStar_List.map
               (fun a  ->
                  let _0_445 = sli a.FStar_Syntax_Syntax.action_name in
                  let _0_444 =
                    let _0_441 =
                      univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
                    FStar_All.pipe_left enclose_universes _0_441 in
                  let _0_443 =
                    term_to_string a.FStar_Syntax_Syntax.action_typ in
                  let _0_442 =
                    term_to_string a.FStar_Syntax_Syntax.action_defn in
                  FStar_Util.format4 "%s%s : %s = %s" _0_445 _0_444 _0_443
                    _0_442)) in
        FStar_All.pipe_right _0_446 (FStar_String.concat ",\n\t") in
      let _0_484 =
        let _0_483 =
          let _0_482 = lid_to_string ed.FStar_Syntax_Syntax.mname in
          let _0_481 =
            let _0_480 =
              let _0_447 = univ_names_to_string ed.FStar_Syntax_Syntax.univs in
              FStar_All.pipe_left enclose_universes _0_447 in
            let _0_479 =
              let _0_478 =
                binders_to_string " " ed.FStar_Syntax_Syntax.binders in
              let _0_477 =
                let _0_476 = term_to_string ed.FStar_Syntax_Syntax.signature in
                let _0_475 =
                  let _0_474 =
                    tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                  let _0_473 =
                    let _0_472 =
                      tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                    let _0_471 =
                      let _0_470 =
                        tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else in
                      let _0_469 =
                        let _0_468 =
                          tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp in
                        let _0_467 =
                          let _0_466 =
                            tscheme_to_string ed.FStar_Syntax_Syntax.stronger in
                          let _0_465 =
                            let _0_464 =
                              tscheme_to_string
                                ed.FStar_Syntax_Syntax.close_wp in
                            let _0_463 =
                              let _0_462 =
                                tscheme_to_string
                                  ed.FStar_Syntax_Syntax.assert_p in
                              let _0_461 =
                                let _0_460 =
                                  tscheme_to_string
                                    ed.FStar_Syntax_Syntax.assume_p in
                                let _0_459 =
                                  let _0_458 =
                                    tscheme_to_string
                                      ed.FStar_Syntax_Syntax.null_wp in
                                  let _0_457 =
                                    let _0_456 =
                                      tscheme_to_string
                                        ed.FStar_Syntax_Syntax.trivial in
                                    let _0_455 =
                                      let _0_454 =
                                        term_to_string
                                          ed.FStar_Syntax_Syntax.repr in
                                      let _0_453 =
                                        let _0_452 =
                                          tscheme_to_string
                                            ed.FStar_Syntax_Syntax.bind_repr in
                                        let _0_451 =
                                          let _0_450 =
                                            tscheme_to_string
                                              ed.FStar_Syntax_Syntax.return_repr in
                                          let _0_449 =
                                            let _0_448 =
                                              actions_to_string
                                                ed.FStar_Syntax_Syntax.actions in
                                            [_0_448] in
                                          _0_450 :: _0_449 in
                                        _0_452 :: _0_451 in
                                      _0_454 :: _0_453 in
                                    _0_456 :: _0_455 in
                                  _0_458 :: _0_457 in
                                _0_460 :: _0_459 in
                              _0_462 :: _0_461 in
                            _0_464 :: _0_463 in
                          _0_466 :: _0_465 in
                        _0_468 :: _0_467 in
                      _0_470 :: _0_469 in
                    _0_472 :: _0_471 in
                  _0_474 :: _0_473 in
                _0_476 :: _0_475 in
              _0_478 :: _0_477 in
            _0_480 :: _0_479 in
          _0_482 :: _0_481 in
        (if for_free then "_for_free " else "") :: _0_483 in
      FStar_Util.format
        "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
        _0_484
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x with
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.LightOff ,uu____1412) -> "#light \"off\""
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.ResetOptions (None ),uu____1413) ->
        "#reset-options"
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.ResetOptions (Some s),uu____1415) ->
        FStar_Util.format1 "#reset-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.SetOptions s,uu____1417) ->
        FStar_Util.format1 "#set-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,univs,tps,k,uu____1422,uu____1423,quals,uu____1425) ->
        let _0_487 = quals_to_string' quals in
        let _0_486 = binders_to_string " " tps in
        let _0_485 = term_to_string k in
        FStar_Util.format4 "%stype %s %s : %s" _0_487 lid.FStar_Ident.str
          _0_486 _0_485
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,univs,t,uu____1435,uu____1436,uu____1437,uu____1438,uu____1439)
        ->
        let uu____1444 = FStar_Options.print_universes () in
        if uu____1444
        then
          let uu____1445 = FStar_Syntax_Subst.open_univ_vars univs t in
          (match uu____1445 with
           | (univs,t) ->
               let _0_489 = univ_names_to_string univs in
               let _0_488 = term_to_string t in
               FStar_Util.format3 "datacon<%s> %s : %s" _0_489
                 lid.FStar_Ident.str _0_488)
        else
          (let _0_490 = term_to_string t in
           FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str _0_490)
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs,t,quals,uu____1455) ->
        let uu____1458 = FStar_Syntax_Subst.open_univ_vars univs t in
        (match uu____1458 with
         | (univs,t) ->
             let _0_494 = quals_to_string' quals in
             let _0_493 =
               let uu____1463 = FStar_Options.print_universes () in
               if uu____1463
               then
                 let _0_491 = univ_names_to_string univs in
                 FStar_Util.format1 "<%s>" _0_491
               else "" in
             let _0_492 = term_to_string t in
             FStar_Util.format4 "%sval %s %s : %s" _0_494 lid.FStar_Ident.str
               _0_493 _0_492)
    | FStar_Syntax_Syntax.Sig_assume (lid,f,uu____1467,uu____1468) ->
        let _0_495 = term_to_string f in
        FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str _0_495
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____1472,uu____1473,qs,uu____1475)
        -> lbs_to_string qs lbs
    | FStar_Syntax_Syntax.Sig_main (e,uu____1483) ->
        let _0_496 = term_to_string e in
        FStar_Util.format1 "let _ = %s" _0_496
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1485,uu____1486,uu____1487)
        ->
        let _0_497 = FStar_List.map sigelt_to_string ses in
        FStar_All.pipe_right _0_497 (FStar_String.concat "\n")
    | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____1496) ->
        eff_decl_to_string false ed
    | FStar_Syntax_Syntax.Sig_new_effect_for_free (ed,uu____1498) ->
        eff_decl_to_string true ed
    | FStar_Syntax_Syntax.Sig_sub_effect (se,r) ->
        let lift_wp =
          match ((se.FStar_Syntax_Syntax.lift_wp),
                  (se.FStar_Syntax_Syntax.lift))
          with
          | (None ,None ) -> failwith "impossible"
          | (Some lift_wp,uu____1507) -> lift_wp
          | (uu____1511,Some lift) -> lift in
        let uu____1516 =
          FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp)
            (Prims.snd lift_wp) in
        (match uu____1516 with
         | (us,t) ->
             let _0_501 = lid_to_string se.FStar_Syntax_Syntax.source in
             let _0_500 = lid_to_string se.FStar_Syntax_Syntax.target in
             let _0_499 = univ_names_to_string us in
             let _0_498 = term_to_string t in
             FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" _0_501 _0_500
               _0_499 _0_498)
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (l,univs,tps,c,uu____1527,flags,uu____1529) ->
        let uu____1534 = FStar_Options.print_universes () in
        if uu____1534
        then
          let uu____1535 =
            let _0_502 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (tps, c)))
                None FStar_Range.dummyRange in
            FStar_Syntax_Subst.open_univ_vars univs _0_502 in
          (match uu____1535 with
           | (univs,t) ->
               let uu____1552 =
                 let uu____1560 =
                   (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
                 match uu____1560 with
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) -> (bs, c)
                 | uu____1585 -> failwith "impossible" in
               (match uu____1552 with
                | (tps,c) ->
                    let _0_506 = sli l in
                    let _0_505 = univ_names_to_string univs in
                    let _0_504 = binders_to_string " " tps in
                    let _0_503 = comp_to_string c in
                    FStar_Util.format4 "effect %s<%s> %s = %s" _0_506 _0_505
                      _0_504 _0_503))
        else
          (let _0_509 = sli l in
           let _0_508 = binders_to_string " " tps in
           let _0_507 = comp_to_string c in
           FStar_Util.format3 "effect %s %s = %s" _0_509 _0_508 _0_507)
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let _0_510 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" _0_510 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1615,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1617;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1619;
                       FStar_Syntax_Syntax.lbdef = uu____1620;_}::[]),uu____1621,uu____1622,uu____1623,uu____1624)
        ->
        let _0_512 = lbname_to_string lb in
        let _0_511 = term_to_string t in
        FStar_Util.format2 "let %s : %s" _0_512 _0_511
    | uu____1642 ->
        let _0_513 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right _0_513 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let _0_516 = sli m.FStar_Syntax_Syntax.name in
    let _0_515 =
      let _0_514 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right _0_514 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" _0_516 _0_515
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___189_1653  ->
    match uu___189_1653 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let _0_518 = FStar_Util.string_of_int i in
        let _0_517 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" _0_518 _0_517
    | FStar_Syntax_Syntax.NM (x,i) ->
        let _0_520 = bv_to_string x in
        let _0_519 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" _0_520 _0_519
    | FStar_Syntax_Syntax.NT (x,t) ->
        let _0_522 = bv_to_string x in
        let _0_521 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" _0_522 _0_521
    | FStar_Syntax_Syntax.UN (i,u) ->
        let _0_524 = FStar_Util.string_of_int i in
        let _0_523 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" _0_524 _0_523
    | FStar_Syntax_Syntax.UD (u,i) ->
        let _0_525 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText _0_525
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let _0_526 = FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right _0_526 (FStar_String.concat "; ")
let abs_ascription_to_string:
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
    Prims.option -> Prims.string
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder () in
    (match ascription with
     | None  -> FStar_Util.string_builder_append strb "None"
     | Some (FStar_Util.Inl lc) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          FStar_Util.string_builder_append strb
            (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name))
     | Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)));
    FStar_Util.string_of_string_builder strb
let list_to_string f elts =
  match elts with
  | [] -> "[]"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "[";
       (let _0_527 = f x in FStar_Util.string_builder_append strb _0_527);
       FStar_List.iter
         (fun x  ->
            FStar_Util.string_builder_append strb "; ";
            (let _0_528 = f x in FStar_Util.string_builder_append strb _0_528))
         xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let _0_529 = f x in FStar_Util.string_builder_append strb _0_529);
       FStar_List.iter
         (fun x  ->
            FStar_Util.string_builder_append strb ", ";
            (let _0_530 = f x in FStar_Util.string_builder_append strb _0_530))
         xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)