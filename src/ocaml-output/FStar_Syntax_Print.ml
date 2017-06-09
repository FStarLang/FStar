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
    let uu____19 =
      let uu____20 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____20 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____19
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____24 = FStar_Options.print_real_names () in
    if uu____24
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____29 =
      let uu____30 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____30 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____29
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
  | uu____109 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____126 -> failwith "get_lid"
let is_infix_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (fst (FStar_List.split infix_prim_ops)) e
let is_unary_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  -> is_prim_op (fst (FStar_List.split unary_prim_ops)) e
let quants: (FStar_Ident.lident* Prims.string) Prims.list =
  [(FStar_Syntax_Const.forall_lid, "forall");
  (FStar_Syntax_Const.exists_lid, "exists")]
type exp = FStar_Syntax_Syntax.term
let is_b2t: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.b2t_lid] t
let is_quant: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op (fst (FStar_List.split quants)) t
let is_ite: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Syntax_Const.ite_lid] t
let is_lex_cons: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Syntax_Const.lexcons_lid] f
let is_lex_top: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Syntax_Const.lextop_lid] f
let is_inr uu___200_173 =
  match uu___200_173 with
  | FStar_Util.Inl uu____176 -> false
  | FStar_Util.Inr uu____177 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___201_208  ->
          match uu___201_208 with
          | (uu____212,Some (FStar_Syntax_Syntax.Implicit uu____213)) ->
              false
          | uu____215 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list option
  =
  fun e  ->
    let uu____226 =
      let uu____227 = FStar_Syntax_Subst.compress e in
      uu____227.FStar_Syntax_Syntax.n in
    match uu____226 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives.fst args1 in
        let uu____273 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____273
        then
          let uu____282 =
            let uu____287 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____287 in
          (match uu____282 with
           | Some xs ->
               let uu____301 =
                 let uu____305 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____305 :: xs in
               Some uu____301
           | None  -> None)
        else None
    | uu____325 ->
        let uu____326 = is_lex_top e in if uu____326 then Some [] else None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____362 = f hd1 in if uu____362 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident* Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____376 = find (fun p  -> FStar_Ident.lid_equals x (fst p)) xs in
      snd uu____376
let infix_prim_op_to_string e =
  let uu____395 = get_lid e in find_lid uu____395 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____407 = get_lid e in find_lid uu____407 unary_prim_ops
let quant_to_string t =
  let uu____419 = get_lid t in find_lid uu____419 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____427) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____430 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____435) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____445 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____445
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___202_448  ->
    match uu___202_448 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____459 = db_to_string x in Prims.strcat "Tm_bvar: " uu____459
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____461 = nm_to_string x in Prims.strcat "Tm_name: " uu____461
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____463 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____463
    | FStar_Syntax_Syntax.Tm_uinst uu____468 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____473 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____474 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____475 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____490 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____498 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____503 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____513 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____529 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____547 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____555 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____566,m) ->
        let uu____604 = FStar_ST.read m in
        (match uu____604 with
         | None  -> "Tm_delayed"
         | Some uu____615 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____620 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____628 = FStar_Options.hide_uvar_nums () in
    if uu____628
    then "?"
    else
      (let uu____630 =
         let uu____631 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____631 FStar_Util.string_of_int in
       Prims.strcat "?" uu____630)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____635 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____636 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____635 uu____636
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____640 = FStar_Options.hide_uvar_nums () in
    if uu____640
    then "?"
    else
      (let uu____642 =
         let uu____643 =
           let uu____644 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____644 FStar_Util.string_of_int in
         let uu____645 =
           let uu____646 = version_to_string (snd u) in
           Prims.strcat ":" uu____646 in
         Prims.strcat uu____643 uu____645 in
       Prims.strcat "?" uu____642)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____658 = FStar_Syntax_Subst.compress_univ u in
      match uu____658 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____664 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____669 =
      let uu____670 = FStar_Options.ugly () in Prims.op_Negation uu____670 in
    if uu____669
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____674 = FStar_Syntax_Subst.compress_univ u in
       match uu____674 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____682 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____682
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____684 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____684 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____693 = univ_to_string u2 in
                let uu____694 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____693 uu____694)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____697 =
             let uu____698 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____698 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____697
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____706 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____706 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____714 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____714 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___203_720  ->
    match uu___203_720 with
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
        let uu____722 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____722
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____725 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____725 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____732 =
          let uu____733 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____733 in
        let uu____735 =
          let uu____736 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____736 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____732 uu____735
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____747 =
          let uu____748 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____748 in
        let uu____750 =
          let uu____751 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____751 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____747 uu____750
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____757 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____757
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
    | uu____764 ->
        let uu____766 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____766 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____776 ->
        let uu____778 = quals_to_string quals in Prims.strcat uu____778 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____826 =
      let uu____827 = FStar_Options.ugly () in Prims.op_Negation uu____827 in
    if uu____826
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____833 = FStar_Options.print_implicits () in
         if uu____833 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____835 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____856,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____883 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____899 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____907  ->
                                 match uu____907 with
                                 | (t1,uu____911) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____899
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____883 (FStar_String.concat "\\/") in
           let uu____914 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____914
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____926 = tag_of_term t in
           let uu____927 = sli m in
           let uu____928 = term_to_string t' in
           let uu____929 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____926 uu____927
             uu____928 uu____929
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____942 = tag_of_term t in
           let uu____943 = term_to_string t' in
           let uu____944 = sli m0 in
           let uu____945 = sli m1 in
           let uu____946 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____942
             uu____943 uu____944 uu____945 uu____946
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____955 = FStar_Range.string_of_range r in
           let uu____956 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____955
             uu____956
       | FStar_Syntax_Syntax.Tm_meta (t,uu____958) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____967) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____986 = FStar_Options.print_universes () in
           if uu____986
           then
             let uu____987 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____987
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1001 = binders_to_string " -> " bs in
           let uu____1002 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1001 uu____1002
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some (FStar_Util.Inl l) when FStar_Options.print_implicits ()
                ->
                let uu____1037 = binders_to_string " " bs in
                let uu____1038 = term_to_string t2 in
                let uu____1039 =
                  let uu____1040 = l.FStar_Syntax_Syntax.comp () in
                  FStar_All.pipe_left comp_to_string uu____1040 in
                FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1037
                  uu____1038 uu____1039
            | Some (FStar_Util.Inr (l,flags)) when
                FStar_Options.print_implicits () ->
                let uu____1053 = binders_to_string " " bs in
                let uu____1054 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____1053 uu____1054 l.FStar_Ident.str
            | uu____1055 ->
                let uu____1062 = binders_to_string " " bs in
                let uu____1063 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1062 uu____1063)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1070 = bv_to_string xt in
           let uu____1071 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1074 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1070 uu____1071 uu____1074
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1093 = term_to_string t in
           let uu____1094 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1093 uu____1094
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1107 = lbs_to_string [] lbs in
           let uu____1108 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1107 uu____1108
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1156 =
                   let uu____1157 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1157
                     (FStar_Util.dflt "default") in
                 let uu____1160 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1156 uu____1160
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1176 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1176 in
           let uu____1177 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1177 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1206 = term_to_string head1 in
           let uu____1207 =
             let uu____1208 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1226  ->
                       match uu____1226 with
                       | (p,wopt,e) ->
                           let uu____1236 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1237 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1239 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1239 in
                           let uu____1240 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1236
                             uu____1237 uu____1240)) in
             FStar_Util.concat_l "\n\t|" uu____1208 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1206 uu____1207
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1247 = FStar_Options.print_universes () in
           if uu____1247
           then
             let uu____1248 = term_to_string t in
             let uu____1249 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1248 uu____1249
           else term_to_string t
       | uu____1251 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1253 =
      let uu____1254 = FStar_Options.ugly () in Prims.op_Negation uu____1254 in
    if uu____1253
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1270 = fv_to_string l in
           let uu____1271 =
             let uu____1272 =
               FStar_List.map
                 (fun uu____1276  ->
                    match uu____1276 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1272 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1270 uu____1271
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1285) ->
           let uu____1290 = FStar_Options.print_bound_var_types () in
           if uu____1290
           then
             let uu____1291 = bv_to_string x1 in
             let uu____1292 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1291 uu____1292
           else
             (let uu____1294 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1294)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1296 = FStar_Options.print_bound_var_types () in
           if uu____1296
           then
             let uu____1297 = bv_to_string x1 in
             let uu____1298 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1297 uu____1298
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1302 = FStar_Options.print_real_names () in
           if uu____1302
           then
             let uu____1303 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1303
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1315 = FStar_Options.print_universes () in
        if uu____1315
        then
          let uu____1319 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1325 =
                      let uu____1328 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1328 in
                    match uu____1325 with
                    | (us,td) ->
                        let uu____1331 =
                          let uu____1338 =
                            let uu____1339 = FStar_Syntax_Subst.compress td in
                            uu____1339.FStar_Syntax_Syntax.n in
                          match uu____1338 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1348,(t,uu____1350)::(d,uu____1352)::[])
                              -> (t, d)
                          | uu____1386 -> failwith "Impossibe" in
                        (match uu____1331 with
                         | (t,d) ->
                             let uu___210_1403 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___210_1403.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___210_1403.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1319)
        else lbs in
      let uu____1407 = quals_to_string' quals in
      let uu____1408 =
        let uu____1409 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1415 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1416 =
                    let uu____1417 = FStar_Options.print_universes () in
                    if uu____1417
                    then
                      let uu____1418 =
                        let uu____1419 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1419 ">" in
                      Prims.strcat "<" uu____1418
                    else "" in
                  let uu____1421 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1422 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1415 uu____1416
                    uu____1421 uu____1422)) in
        FStar_Util.concat_l "\n and " uu____1409 in
      FStar_Util.format3 "%slet %s %s" uu____1407
        (if fst lbs1 then "rec" else "") uu____1408
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1428 = FStar_Options.print_effect_args () in
    if uu____1428
    then
      let uu____1429 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1429
    else
      (let uu____1431 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1432 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1431 uu____1432)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___204_1434  ->
      match uu___204_1434 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1436 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1440 =
        let uu____1441 = FStar_Options.ugly () in
        Prims.op_Negation uu____1441 in
      if uu____1440
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1445 = b in
         match uu____1445 with
         | (a,imp) ->
             let uu____1448 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1448
             then
               let uu____1449 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1449
             else
               (let uu____1451 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1452 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1452) in
                if uu____1451
                then
                  let uu____1453 = nm_to_string a in
                  imp_to_string uu____1453 imp
                else
                  (let uu____1455 =
                     let uu____1456 = nm_to_string a in
                     let uu____1457 =
                       let uu____1458 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1458 in
                     Prims.strcat uu____1456 uu____1457 in
                   imp_to_string uu____1455 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1464 = FStar_Options.print_implicits () in
        if uu____1464 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1466 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1466 (FStar_String.concat sep)
      else
        (let uu____1471 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1471 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___205_1475  ->
    match uu___205_1475 with
    | (a,imp) ->
        let uu____1483 = term_to_string a in imp_to_string uu____1483 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1486 = FStar_Options.print_implicits () in
      if uu____1486 then args else filter_imp args in
    let uu____1490 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1490 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1498 =
      let uu____1499 = FStar_Options.ugly () in Prims.op_Negation uu____1499 in
    if uu____1498
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1504) ->
           let uu____1511 =
             let uu____1512 = FStar_Syntax_Subst.compress t in
             uu____1512.FStar_Syntax_Syntax.n in
           (match uu____1511 with
            | FStar_Syntax_Syntax.Tm_type uu____1515 when
                let uu____1516 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1516 -> term_to_string t
            | uu____1517 ->
                let uu____1518 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____1518)
       | FStar_Syntax_Syntax.GTotal (t,uu____1520) ->
           let uu____1527 =
             let uu____1528 = FStar_Syntax_Subst.compress t in
             uu____1528.FStar_Syntax_Syntax.n in
           (match uu____1527 with
            | FStar_Syntax_Syntax.Tm_type uu____1531 when
                let uu____1532 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1532 -> term_to_string t
            | uu____1533 ->
                let uu____1534 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____1534)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1537 = FStar_Options.print_effect_args () in
             if uu____1537
             then
               let uu____1538 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1539 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1540 =
                 let uu____1541 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1541 (FStar_String.concat ", ") in
               let uu____1553 =
                 let uu____1554 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1554 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1538
                 uu____1539 uu____1540 uu____1553
             else
               (let uu____1560 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___206_1562  ->
                           match uu___206_1562 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1563 -> false)))
                    &&
                    (let uu____1564 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1564) in
                if uu____1560
                then
                  let uu____1565 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1565
                else
                  (let uu____1567 =
                     ((let uu____1568 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1568) &&
                        (let uu____1569 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1569))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1567
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1571 =
                        (let uu____1572 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1572) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___207_1574  ->
                                   match uu___207_1574 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1575 -> false))) in
                      if uu____1571
                      then
                        let uu____1576 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1576
                      else
                        (let uu____1578 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1579 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1578 uu____1579)))) in
           let dec =
             let uu____1581 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___208_1585  ->
                       match uu___208_1585 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1590 =
                             let uu____1591 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1591 in
                           [uu____1590]
                       | uu____1592 -> [])) in
             FStar_All.pipe_right uu____1581 (FStar_String.concat " ") in
           FStar_Util.format2 "%s%s" basic dec)
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
    | FStar_Syntax_Syntax.DECREASES uu____1595 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1604 = FStar_Options.print_universes () in
    if uu____1604 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1609 =
      let uu____1610 = FStar_Options.ugly () in Prims.op_Negation uu____1610 in
    if uu____1609
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1614 = s in
       match uu____1614 with
       | (us,t) ->
           let uu____1619 =
             let uu____1620 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1620 in
           let uu____1621 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1619 uu____1621)
let eff_decl_to_string':
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____1636 =
            let uu____1637 = FStar_Options.ugly () in
            Prims.op_Negation uu____1637 in
          if uu____1636
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1647 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____1652 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____1653 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____1654 =
                           let uu____1655 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____1655 in
                         let uu____1656 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____1657 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____1652
                           uu____1653 uu____1654 uu____1656 uu____1657)) in
               FStar_All.pipe_right uu____1647 (FStar_String.concat ",\n\t") in
             let uu____1659 =
               let uu____1661 =
                 let uu____1663 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1664 =
                   let uu____1666 =
                     let uu____1667 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1667 in
                   let uu____1668 =
                     let uu____1670 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1671 =
                       let uu____1673 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1674 =
                         let uu____1676 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1677 =
                           let uu____1679 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1680 =
                             let uu____1682 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1683 =
                               let uu____1685 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1686 =
                                 let uu____1688 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1689 =
                                   let uu____1691 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1692 =
                                     let uu____1694 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1695 =
                                       let uu____1697 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1698 =
                                         let uu____1700 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1701 =
                                           let uu____1703 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1704 =
                                             let uu____1706 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1707 =
                                               let uu____1709 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1710 =
                                                 let uu____1712 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1713 =
                                                   let uu____1715 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1715] in
                                                 uu____1712 :: uu____1713 in
                                               uu____1709 :: uu____1710 in
                                             uu____1706 :: uu____1707 in
                                           uu____1703 :: uu____1704 in
                                         uu____1700 :: uu____1701 in
                                       uu____1697 :: uu____1698 in
                                     uu____1694 :: uu____1695 in
                                   uu____1691 :: uu____1692 in
                                 uu____1688 :: uu____1689 in
                               uu____1685 :: uu____1686 in
                             uu____1682 :: uu____1683 in
                           uu____1679 :: uu____1680 in
                         uu____1676 :: uu____1677 in
                       uu____1673 :: uu____1674 in
                     uu____1670 :: uu____1671 in
                   uu____1666 :: uu____1668 in
                 uu____1663 :: uu____1664 in
               (if for_free then "_for_free " else "") :: uu____1661 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1659)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1726 =
      let uu____1727 = FStar_Options.ugly () in Prims.op_Negation uu____1727 in
    if uu____1726
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1732 -> ""
    else
      (match x.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
           "#light \"off\""
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           (None )) -> "#reset-options"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           (Some s)) -> FStar_Util.format1 "#reset-options \"%s\"" s
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
           FStar_Util.format1 "#set-options \"%s\"" s
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (lid,univs1,tps,k,uu____1741,uu____1742) ->
           let uu____1747 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1748 = binders_to_string " " tps in
           let uu____1749 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1747
             lid.FStar_Ident.str uu____1748 uu____1749
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1753,uu____1754,uu____1755) ->
           let uu____1758 = FStar_Options.print_universes () in
           if uu____1758
           then
             let uu____1759 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1759 with
              | (univs2,t1) ->
                  let uu____1764 = univ_names_to_string univs2 in
                  let uu____1765 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1764
                    lid.FStar_Ident.str uu____1765)
           else
             (let uu____1767 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1767)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1771 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1771 with
            | (univs2,t1) ->
                let uu____1776 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1777 =
                  let uu____1778 = FStar_Options.print_universes () in
                  if uu____1778
                  then
                    let uu____1779 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1779
                  else "" in
                let uu____1781 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1776
                  lid.FStar_Ident.str uu____1777 uu____1781)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____1783,f) ->
           let uu____1785 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1785
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1787,uu____1788) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1794 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1794
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1796) ->
           let uu____1801 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1801 (FStar_String.concat "\n")
       | FStar_Syntax_Syntax.Sig_new_effect ed ->
           eff_decl_to_string' false x.FStar_Syntax_Syntax.sigrng
             x.FStar_Syntax_Syntax.sigquals ed
       | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
           eff_decl_to_string' true x.FStar_Syntax_Syntax.sigrng
             x.FStar_Syntax_Syntax.sigquals ed
       | FStar_Syntax_Syntax.Sig_sub_effect se ->
           let lift_wp =
             match ((se.FStar_Syntax_Syntax.lift_wp),
                     (se.FStar_Syntax_Syntax.lift))
             with
             | (None ,None ) -> failwith "impossible"
             | (Some lift_wp,uu____1813) -> lift_wp
             | (uu____1817,Some lift) -> lift in
           let uu____1822 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1822 with
            | (us,t) ->
                let uu____1829 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1830 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1831 = univ_names_to_string us in
                let uu____1832 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1829
                  uu____1830 uu____1831 uu____1832)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1840 = FStar_Options.print_universes () in
           if uu____1840
           then
             let uu____1841 =
               let uu____1844 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1844 in
             (match uu____1841 with
              | (univs2,t) ->
                  let uu____1855 =
                    let uu____1863 =
                      let uu____1864 = FStar_Syntax_Subst.compress t in
                      uu____1864.FStar_Syntax_Syntax.n in
                    match uu____1863 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1891 -> failwith "impossible" in
                  (match uu____1855 with
                   | (tps1,c1) ->
                       let uu____1911 = sli l in
                       let uu____1912 = univ_names_to_string univs2 in
                       let uu____1913 = binders_to_string " " tps1 in
                       let uu____1914 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1911
                         uu____1912 uu____1913 uu____1914))
           else
             (let uu____1916 = sli l in
              let uu____1917 = binders_to_string " " tps in
              let uu____1918 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1916 uu____1917
                uu____1918))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1925 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1925 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1929,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1931;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1933;
                       FStar_Syntax_Syntax.lbdef = uu____1934;_}::[]),uu____1935,uu____1936)
        ->
        let uu____1952 = lbname_to_string lb in
        let uu____1953 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1952 uu____1953
    | uu____1954 ->
        let uu____1955 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1955 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1964 = sli m.FStar_Syntax_Syntax.name in
    let uu____1965 =
      let uu____1966 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1966 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1964 uu____1965
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___209_1971  ->
    match uu___209_1971 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1974 = FStar_Util.string_of_int i in
        let uu____1975 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1974 uu____1975
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1978 = bv_to_string x in
        let uu____1979 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1978 uu____1979
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1986 = bv_to_string x in
        let uu____1987 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1986 uu____1987
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1990 = FStar_Util.string_of_int i in
        let uu____1991 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1990 uu____1991
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1994 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1994
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1998 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1998 (FStar_String.concat "; ")
let abs_ascription_to_string:
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either option ->
    Prims.string
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
       (let uu____2048 = f x in
        FStar_Util.string_builder_append strb uu____2048);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2052 = f x1 in
             FStar_Util.string_builder_append strb uu____2052)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2081 = f x in
        FStar_Util.string_builder_append strb uu____2081);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2085 = f x1 in
             FStar_Util.string_builder_append strb uu____2085)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)