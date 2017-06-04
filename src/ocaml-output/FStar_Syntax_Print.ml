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
let is_inr uu___208_173 =
  match uu___208_173 with
  | FStar_Util.Inl uu____176 -> false
  | FStar_Util.Inr uu____177 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___209_208  ->
          match uu___209_208 with
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
  fun uu___210_448  ->
    match uu___210_448 with
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
    | FStar_Syntax_Syntax.Tm_delayed (uu____564,m) ->
        let uu____602 = FStar_ST.read m in
        (match uu____602 with
         | None  -> "Tm_delayed"
         | Some uu____613 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____618 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____626 = FStar_Options.hide_uvar_nums () in
    if uu____626
    then "?"
    else
      (let uu____628 =
         let uu____629 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____629 FStar_Util.string_of_int in
       Prims.strcat "?" uu____628)
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____633 = FStar_Options.hide_uvar_nums () in
    if uu____633
    then "?"
    else
      (let uu____635 =
         let uu____636 = FStar_Syntax_Unionfind.univ_uvar_id u in
         FStar_All.pipe_right uu____636 FStar_Util.string_of_int in
       Prims.strcat "?" uu____635)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____646 = FStar_Syntax_Subst.compress_univ u in
      match uu____646 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____652 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____657 =
      let uu____658 = FStar_Options.ugly () in Prims.op_Negation uu____658 in
    if uu____657
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____662 = FStar_Syntax_Subst.compress_univ u in
       match uu____662 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____668 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____668
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____670 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____670 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____679 = univ_to_string u2 in
                let uu____680 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____679 uu____680)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____683 =
             let uu____684 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____684 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____683
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____692 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____692 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____700 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____700 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___211_706  ->
    match uu___211_706 with
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
        let uu____708 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____708
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____711 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____711 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____718 =
          let uu____719 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____719 in
        let uu____721 =
          let uu____722 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____722 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____718 uu____721
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____733 =
          let uu____734 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____734 in
        let uu____736 =
          let uu____737 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____737 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____733 uu____736
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____743 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____743
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
    | uu____750 ->
        let uu____752 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____752 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____762 ->
        let uu____764 = quals_to_string quals in Prims.strcat uu____764 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____812 =
      let uu____813 = FStar_Options.ugly () in Prims.op_Negation uu____813 in
    if uu____812
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____819 = FStar_Options.print_implicits () in
         if uu____819 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____821 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____842,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____869 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____885 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____893  ->
                                 match uu____893 with
                                 | (t1,uu____897) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____885
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____869 (FStar_String.concat "\\/") in
           let uu____900 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____900
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____912 = tag_of_term t in
           let uu____913 = sli m in
           let uu____914 = term_to_string t' in
           let uu____915 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____912 uu____913
             uu____914 uu____915
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____928 = tag_of_term t in
           let uu____929 = term_to_string t' in
           let uu____930 = sli m0 in
           let uu____931 = sli m1 in
           let uu____932 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____928
             uu____929 uu____930 uu____931 uu____932
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____941 = FStar_Range.string_of_range r in
           let uu____942 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____941
             uu____942
       | FStar_Syntax_Syntax.Tm_meta (t,uu____944) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____953) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____968 = FStar_Options.print_universes () in
           if uu____968
           then
             let uu____969 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____969
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____983 = binders_to_string " -> " bs in
           let uu____984 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____983 uu____984
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some (FStar_Util.Inl l) when FStar_Options.print_implicits ()
                ->
                let uu____1019 = binders_to_string " " bs in
                let uu____1020 = term_to_string t2 in
                let uu____1021 =
                  let uu____1022 = l.FStar_Syntax_Syntax.comp () in
                  FStar_All.pipe_left comp_to_string uu____1022 in
                FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1019
                  uu____1020 uu____1021
            | Some (FStar_Util.Inr (l,flags)) when
                FStar_Options.print_implicits () ->
                let uu____1035 = binders_to_string " " bs in
                let uu____1036 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____1035 uu____1036 l.FStar_Ident.str
            | uu____1037 ->
                let uu____1044 = binders_to_string " " bs in
                let uu____1045 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1044 uu____1045)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1052 = bv_to_string xt in
           let uu____1053 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1056 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1052 uu____1053 uu____1056
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1075 = term_to_string t in
           let uu____1076 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1075 uu____1076
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1089 = lbs_to_string [] lbs in
           let uu____1090 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1089 uu____1090
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1138 =
                   let uu____1139 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1139
                     (FStar_Util.dflt "default") in
                 let uu____1142 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1138 uu____1142
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1158 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1158 in
           let uu____1159 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1159 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1188 = term_to_string head1 in
           let uu____1189 =
             let uu____1190 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1208  ->
                       match uu____1208 with
                       | (p,wopt,e) ->
                           let uu____1218 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1219 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1221 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1221 in
                           let uu____1222 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1218
                             uu____1219 uu____1222)) in
             FStar_Util.concat_l "\n\t|" uu____1190 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1188 uu____1189
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1229 = FStar_Options.print_universes () in
           if uu____1229
           then
             let uu____1230 = term_to_string t in
             let uu____1231 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1230 uu____1231
           else term_to_string t
       | uu____1233 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1235 =
      let uu____1236 = FStar_Options.ugly () in Prims.op_Negation uu____1236 in
    if uu____1235
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1252 = fv_to_string l in
           let uu____1253 =
             let uu____1254 =
               FStar_List.map
                 (fun uu____1258  ->
                    match uu____1258 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1254 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1252 uu____1253
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1267) ->
           let uu____1272 = FStar_Options.print_bound_var_types () in
           if uu____1272
           then
             let uu____1273 = bv_to_string x1 in
             let uu____1274 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1273 uu____1274
           else
             (let uu____1276 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1276)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1278 = FStar_Options.print_bound_var_types () in
           if uu____1278
           then
             let uu____1279 = bv_to_string x1 in
             let uu____1280 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1279 uu____1280
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1284 = FStar_Options.print_real_names () in
           if uu____1284
           then
             let uu____1285 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1285
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1297 = FStar_Options.print_universes () in
        if uu____1297
        then
          let uu____1301 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1307 =
                      let uu____1310 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1310 in
                    match uu____1307 with
                    | (us,td) ->
                        let uu____1313 =
                          let uu____1320 =
                            let uu____1321 = FStar_Syntax_Subst.compress td in
                            uu____1321.FStar_Syntax_Syntax.n in
                          match uu____1320 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1330,(t,uu____1332)::(d,uu____1334)::[])
                              -> (t, d)
                          | uu____1368 -> failwith "Impossibe" in
                        (match uu____1313 with
                         | (t,d) ->
                             let uu___218_1385 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___218_1385.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___218_1385.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1301)
        else lbs in
      let uu____1389 = quals_to_string' quals in
      let uu____1390 =
        let uu____1391 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1397 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1398 =
                    let uu____1399 = FStar_Options.print_universes () in
                    if uu____1399
                    then
                      let uu____1400 =
                        let uu____1401 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1401 ">" in
                      Prims.strcat "<" uu____1400
                    else "" in
                  let uu____1403 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1404 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1397 uu____1398
                    uu____1403 uu____1404)) in
        FStar_Util.concat_l "\n and " uu____1391 in
      FStar_Util.format3 "%slet %s %s" uu____1389
        (if fst lbs1 then "rec" else "") uu____1390
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1410 = FStar_Options.print_effect_args () in
    if uu____1410
    then
      let uu____1411 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1411
    else
      (let uu____1413 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1414 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1413 uu____1414)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___212_1416  ->
      match uu___212_1416 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1418 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1422 =
        let uu____1423 = FStar_Options.ugly () in
        Prims.op_Negation uu____1423 in
      if uu____1422
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1427 = b in
         match uu____1427 with
         | (a,imp) ->
             let uu____1430 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1430
             then
               let uu____1431 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1431
             else
               (let uu____1433 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1434 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1434) in
                if uu____1433
                then
                  let uu____1435 = nm_to_string a in
                  imp_to_string uu____1435 imp
                else
                  (let uu____1437 =
                     let uu____1438 = nm_to_string a in
                     let uu____1439 =
                       let uu____1440 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1440 in
                     Prims.strcat uu____1438 uu____1439 in
                   imp_to_string uu____1437 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1446 = FStar_Options.print_implicits () in
        if uu____1446 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1448 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1448 (FStar_String.concat sep)
      else
        (let uu____1453 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1453 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___213_1457  ->
    match uu___213_1457 with
    | (a,imp) ->
        let uu____1465 = term_to_string a in imp_to_string uu____1465 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1468 = FStar_Options.print_implicits () in
      if uu____1468 then args else filter_imp args in
    let uu____1472 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1472 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1480 =
      let uu____1481 = FStar_Options.ugly () in Prims.op_Negation uu____1481 in
    if uu____1480
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1486) ->
           let uu____1493 =
             let uu____1494 = FStar_Syntax_Subst.compress t in
             uu____1494.FStar_Syntax_Syntax.n in
           (match uu____1493 with
            | FStar_Syntax_Syntax.Tm_type uu____1497 when
                let uu____1498 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1498 -> term_to_string t
            | uu____1499 ->
                let uu____1500 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____1500)
       | FStar_Syntax_Syntax.GTotal (t,uu____1502) ->
           let uu____1509 =
             let uu____1510 = FStar_Syntax_Subst.compress t in
             uu____1510.FStar_Syntax_Syntax.n in
           (match uu____1509 with
            | FStar_Syntax_Syntax.Tm_type uu____1513 when
                let uu____1514 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1514 -> term_to_string t
            | uu____1515 ->
                let uu____1516 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____1516)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1519 = FStar_Options.print_effect_args () in
             if uu____1519
             then
               let uu____1520 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1521 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1522 =
                 let uu____1523 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1523 (FStar_String.concat ", ") in
               let uu____1535 =
                 let uu____1536 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1536 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1520
                 uu____1521 uu____1522 uu____1535
             else
               (let uu____1542 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___214_1544  ->
                           match uu___214_1544 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1545 -> false)))
                    &&
                    (let uu____1546 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1546) in
                if uu____1542
                then
                  let uu____1547 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1547
                else
                  (let uu____1549 =
                     ((let uu____1550 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1550) &&
                        (let uu____1551 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1551))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1549
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1553 =
                        (let uu____1554 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1554) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___215_1556  ->
                                   match uu___215_1556 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1557 -> false))) in
                      if uu____1553
                      then
                        let uu____1558 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1558
                      else
                        (let uu____1560 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1561 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1560 uu____1561)))) in
           let dec =
             let uu____1563 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___216_1567  ->
                       match uu___216_1567 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1572 =
                             let uu____1573 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1573 in
                           [uu____1572]
                       | uu____1574 -> [])) in
             FStar_All.pipe_right uu____1563 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1577 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1586 = FStar_Options.print_universes () in
    if uu____1586 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1591 =
      let uu____1592 = FStar_Options.ugly () in Prims.op_Negation uu____1592 in
    if uu____1591
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1596 = s in
       match uu____1596 with
       | (us,t) ->
           let uu____1601 =
             let uu____1602 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1602 in
           let uu____1603 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1601 uu____1603)
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
          let uu____1618 =
            let uu____1619 = FStar_Options.ugly () in
            Prims.op_Negation uu____1619 in
          if uu____1618
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1629 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____1634 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____1635 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____1636 =
                           let uu____1637 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____1637 in
                         let uu____1638 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____1639 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____1634
                           uu____1635 uu____1636 uu____1638 uu____1639)) in
               FStar_All.pipe_right uu____1629 (FStar_String.concat ",\n\t") in
             let uu____1641 =
               let uu____1643 =
                 let uu____1645 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1646 =
                   let uu____1648 =
                     let uu____1649 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1649 in
                   let uu____1650 =
                     let uu____1652 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1653 =
                       let uu____1655 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1656 =
                         let uu____1658 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1659 =
                           let uu____1661 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1662 =
                             let uu____1664 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1665 =
                               let uu____1667 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1668 =
                                 let uu____1670 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1671 =
                                   let uu____1673 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1674 =
                                     let uu____1676 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1677 =
                                       let uu____1679 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1680 =
                                         let uu____1682 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1683 =
                                           let uu____1685 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1686 =
                                             let uu____1688 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1689 =
                                               let uu____1691 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1692 =
                                                 let uu____1694 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1695 =
                                                   let uu____1697 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1697] in
                                                 uu____1694 :: uu____1695 in
                                               uu____1691 :: uu____1692 in
                                             uu____1688 :: uu____1689 in
                                           uu____1685 :: uu____1686 in
                                         uu____1682 :: uu____1683 in
                                       uu____1679 :: uu____1680 in
                                     uu____1676 :: uu____1677 in
                                   uu____1673 :: uu____1674 in
                                 uu____1670 :: uu____1671 in
                               uu____1667 :: uu____1668 in
                             uu____1664 :: uu____1665 in
                           uu____1661 :: uu____1662 in
                         uu____1658 :: uu____1659 in
                       uu____1655 :: uu____1656 in
                     uu____1652 :: uu____1653 in
                   uu____1648 :: uu____1650 in
                 uu____1645 :: uu____1646 in
               (if for_free then "_for_free " else "") :: uu____1643 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1641)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1708 =
      let uu____1709 = FStar_Options.ugly () in Prims.op_Negation uu____1709 in
    if uu____1708
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1714 -> ""
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
           (lid,univs1,tps,k,uu____1723,uu____1724) ->
           let uu____1729 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1730 = binders_to_string " " tps in
           let uu____1731 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1729
             lid.FStar_Ident.str uu____1730 uu____1731
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1735,uu____1736,uu____1737) ->
           let uu____1740 = FStar_Options.print_universes () in
           if uu____1740
           then
             let uu____1741 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1741 with
              | (univs2,t1) ->
                  let uu____1746 = univ_names_to_string univs2 in
                  let uu____1747 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1746
                    lid.FStar_Ident.str uu____1747)
           else
             (let uu____1749 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1749)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1753 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1753 with
            | (univs2,t1) ->
                let uu____1758 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1759 =
                  let uu____1760 = FStar_Options.print_universes () in
                  if uu____1760
                  then
                    let uu____1761 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1761
                  else "" in
                let uu____1763 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1758
                  lid.FStar_Ident.str uu____1759 uu____1763)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____1766 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1766
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1768,uu____1769) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1775 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1775
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1777) ->
           let uu____1782 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1782 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1794) -> lift_wp
             | (uu____1798,Some lift) -> lift in
           let uu____1803 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1803 with
            | (us,t) ->
                let uu____1810 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1811 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1812 = univ_names_to_string us in
                let uu____1813 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1810
                  uu____1811 uu____1812 uu____1813)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1821 = FStar_Options.print_universes () in
           if uu____1821
           then
             let uu____1822 =
               let uu____1825 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1825 in
             (match uu____1822 with
              | (univs2,t) ->
                  let uu____1836 =
                    let uu____1844 =
                      let uu____1845 = FStar_Syntax_Subst.compress t in
                      uu____1845.FStar_Syntax_Syntax.n in
                    match uu____1844 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1872 -> failwith "impossible" in
                  (match uu____1836 with
                   | (tps1,c1) ->
                       let uu____1892 = sli l in
                       let uu____1893 = univ_names_to_string univs2 in
                       let uu____1894 = binders_to_string " " tps1 in
                       let uu____1895 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1892
                         uu____1893 uu____1894 uu____1895))
           else
             (let uu____1897 = sli l in
              let uu____1898 = binders_to_string " " tps in
              let uu____1899 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1897 uu____1898
                uu____1899))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1906 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1906 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1910,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1912;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1914;
                       FStar_Syntax_Syntax.lbdef = uu____1915;_}::[]),uu____1916,uu____1917)
        ->
        let uu____1933 = lbname_to_string lb in
        let uu____1934 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1933 uu____1934
    | uu____1935 ->
        let uu____1936 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1936 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1945 = sli m.FStar_Syntax_Syntax.name in
    let uu____1946 =
      let uu____1947 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1947 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1945 uu____1946
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___217_1952  ->
    match uu___217_1952 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1955 = FStar_Util.string_of_int i in
        let uu____1956 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1955 uu____1956
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1959 = bv_to_string x in
        let uu____1960 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1959 uu____1960
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1967 = bv_to_string x in
        let uu____1968 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1967 uu____1968
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1971 = FStar_Util.string_of_int i in
        let uu____1972 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1971 uu____1972
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1975 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1975
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1979 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1979 (FStar_String.concat "; ")
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
       (let uu____2029 = f x in
        FStar_Util.string_builder_append strb uu____2029);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2033 = f x1 in
             FStar_Util.string_builder_append strb uu____2033)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2062 = f x in
        FStar_Util.string_builder_append strb uu____2062);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2066 = f x1 in
             FStar_Util.string_builder_append strb uu____2066)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)