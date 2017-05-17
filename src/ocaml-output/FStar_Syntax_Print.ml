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
let is_inr uu___210_173 =
  match uu___210_173 with
  | FStar_Util.Inl uu____176 -> false
  | FStar_Util.Inr uu____177 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___211_208  ->
          match uu___211_208 with
          | (uu____212,Some (FStar_Syntax_Syntax.Implicit uu____213)) ->
              false
          | uu____215 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list Prims.option
  =
  fun e  ->
    let uu____226 =
      let uu____227 = FStar_Syntax_Subst.compress e in
      uu____227.FStar_Syntax_Syntax.n in
    match uu____226 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map Prims.fst args1 in
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
      let uu____376 =
        find (fun p  -> FStar_Ident.lid_equals x (Prims.fst p)) xs in
      Prims.snd uu____376
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
  fun uu___212_448  ->
    match uu___212_448 with
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
let uvar_to_string u =
  let uu____632 = FStar_Options.hide_uvar_nums () in
  if uu____632
  then "?"
  else
    (let uu____634 =
       let uu____635 = FStar_Unionfind.uvar_id u in
       FStar_All.pipe_right uu____635 FStar_Util.string_of_int in
     Prims.strcat "?" uu____634)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe Prims.option)
  =
  fun n1  ->
    fun u  ->
      let uu____645 = FStar_Syntax_Subst.compress_univ u in
      match uu____645 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____651 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____656 = FStar_Syntax_Subst.compress_univ u in
    match uu____656 with
    | FStar_Syntax_Syntax.U_unif u1 -> uvar_to_string u1
    | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____663 = FStar_Util.string_of_int x in
        Prims.strcat "@" uu____663
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____665 = int_of_univ (Prims.parse_int "1") u1 in
        (match uu____665 with
         | (n1,None ) -> FStar_Util.string_of_int n1
         | (n1,Some u2) ->
             let uu____674 = univ_to_string u2 in
             let uu____675 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "(%s + %s)" uu____674 uu____675)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____678 =
          let uu____679 = FStar_List.map univ_to_string us in
          FStar_All.pipe_right uu____679 (FStar_String.concat ", ") in
        FStar_Util.format1 "(max %s)" uu____678
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____687 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____687 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____695 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____695 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___213_701  ->
    match uu___213_701 with
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
        let uu____703 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____703
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____706 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____706 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____713 =
          let uu____714 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____714 in
        let uu____716 =
          let uu____717 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____717 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____713 uu____716
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____728 =
          let uu____729 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____729 in
        let uu____731 =
          let uu____732 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____732 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____728 uu____731
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____738 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____738
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
    | uu____745 ->
        let uu____747 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____747 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____757 ->
        let uu____759 = quals_to_string quals in Prims.strcat uu____759 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____811 =
      let uu____812 = FStar_Options.ugly () in Prims.op_Negation uu____812 in
    if uu____811
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____818 = FStar_Options.print_implicits () in
         if uu____818 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____820 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____841,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____868 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____884 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____892  ->
                                 match uu____892 with
                                 | (t1,uu____896) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____884
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____868 (FStar_String.concat "\\/") in
           let uu____899 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____899
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____911 = tag_of_term t in
           let uu____912 = sli m in
           let uu____913 = term_to_string t' in
           let uu____914 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____911 uu____912
             uu____913 uu____914
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____927 = tag_of_term t in
           let uu____928 = term_to_string t' in
           let uu____929 = sli m0 in
           let uu____930 = sli m1 in
           let uu____931 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____927
             uu____928 uu____929 uu____930 uu____931
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____940 = FStar_Range.string_of_range r in
           let uu____941 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____940
             uu____941
       | FStar_Syntax_Syntax.Tm_meta (t,uu____943) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____952) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____970 = FStar_Options.print_universes () in
           if uu____970
           then
             let uu____971 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____971
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____985 = binders_to_string " -> " bs in
           let uu____986 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____985 uu____986
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some (FStar_Util.Inl l) when FStar_Options.print_implicits ()
                ->
                let uu____1021 = binders_to_string " " bs in
                let uu____1022 = term_to_string t2 in
                let uu____1023 =
                  let uu____1024 = l.FStar_Syntax_Syntax.comp () in
                  FStar_All.pipe_left comp_to_string uu____1024 in
                FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1021
                  uu____1022 uu____1023
            | Some (FStar_Util.Inr (l,flags)) when
                FStar_Options.print_implicits () ->
                let uu____1037 = binders_to_string " " bs in
                let uu____1038 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____1037 uu____1038 l.FStar_Ident.str
            | uu____1039 ->
                let uu____1046 = binders_to_string " " bs in
                let uu____1047 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1046 uu____1047)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1054 = bv_to_string xt in
           let uu____1055 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1058 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1054 uu____1055 uu____1058
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1077 = term_to_string t in
           let uu____1078 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1077 uu____1078
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1091 = lbs_to_string [] lbs in
           let uu____1092 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1091 uu____1092
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1140 =
                   let uu____1141 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1141
                     (FStar_Util.dflt "default") in
                 let uu____1144 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1140 uu____1144
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1160 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1160 in
           let uu____1161 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1161 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1190 = term_to_string head1 in
           let uu____1191 =
             let uu____1192 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1210  ->
                       match uu____1210 with
                       | (p,wopt,e) ->
                           let uu____1220 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1221 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1223 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1223 in
                           let uu____1224 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1220
                             uu____1221 uu____1224)) in
             FStar_Util.concat_l "\n\t|" uu____1192 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1190 uu____1191
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1231 = FStar_Options.print_universes () in
           if uu____1231
           then
             let uu____1232 = term_to_string t in
             let uu____1233 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1232 uu____1233
           else term_to_string t
       | uu____1235 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
        let uu____1249 = fv_to_string l in
        let uu____1250 =
          let uu____1251 =
            FStar_List.map
              (fun uu____1255  ->
                 match uu____1255 with
                 | (x1,b) ->
                     let p = pat_to_string x1 in
                     if b then Prims.strcat "#" p else p) pats in
          FStar_All.pipe_right uu____1251 (FStar_String.concat " ") in
        FStar_Util.format2 "(%s %s)" uu____1249 uu____1250
    | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1264) ->
        let uu____1269 = FStar_Options.print_bound_var_types () in
        if uu____1269
        then
          let uu____1270 = bv_to_string x1 in
          let uu____1271 = term_to_string x1.FStar_Syntax_Syntax.sort in
          FStar_Util.format2 ".%s:%s" uu____1270 uu____1271
        else
          (let uu____1273 = bv_to_string x1 in
           FStar_Util.format1 ".%s" uu____1273)
    | FStar_Syntax_Syntax.Pat_var x1 ->
        let uu____1275 = FStar_Options.print_bound_var_types () in
        if uu____1275
        then
          let uu____1276 = bv_to_string x1 in
          let uu____1277 = term_to_string x1.FStar_Syntax_Syntax.sort in
          FStar_Util.format2 "%s:%s" uu____1276 uu____1277
        else bv_to_string x1
    | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
    | FStar_Syntax_Syntax.Pat_wild x1 ->
        let uu____1281 = FStar_Options.print_real_names () in
        if uu____1281
        then
          let uu____1282 = bv_to_string x1 in
          Prims.strcat "Pat_wild " uu____1282
        else "_"
    | FStar_Syntax_Syntax.Pat_disj ps ->
        let uu____1288 = FStar_List.map pat_to_string ps in
        FStar_Util.concat_l " | " uu____1288
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1300 = FStar_Options.print_universes () in
        if uu____1300
        then
          let uu____1304 =
            FStar_All.pipe_right (Prims.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1310 =
                      let uu____1313 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1313 in
                    match uu____1310 with
                    | (us,td) ->
                        let uu____1316 =
                          let uu____1323 =
                            let uu____1324 = FStar_Syntax_Subst.compress td in
                            uu____1324.FStar_Syntax_Syntax.n in
                          match uu____1323 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1333,(t,uu____1335)::(d,uu____1337)::[])
                              -> (t, d)
                          | uu____1371 -> failwith "Impossibe" in
                        (match uu____1316 with
                         | (t,d) ->
                             let uu___220_1388 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___220_1388.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___220_1388.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((Prims.fst lbs), uu____1304)
        else lbs in
      let uu____1392 = quals_to_string' quals in
      let uu____1393 =
        let uu____1394 =
          FStar_All.pipe_right (Prims.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1400 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1401 =
                    let uu____1402 = FStar_Options.print_universes () in
                    if uu____1402
                    then
                      let uu____1403 =
                        let uu____1404 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1404 ">" in
                      Prims.strcat "<" uu____1403
                    else "" in
                  let uu____1406 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1407 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1400 uu____1401
                    uu____1406 uu____1407)) in
        FStar_Util.concat_l "\n and " uu____1394 in
      FStar_Util.format3 "%slet %s %s" uu____1392
        (if Prims.fst lbs1 then "rec" else "") uu____1393
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1413 = FStar_Options.print_effect_args () in
    if uu____1413
    then
      let uu____1414 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1414
    else
      (let uu____1416 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1417 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1416 uu____1417)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.string
  =
  fun s  ->
    fun uu___214_1419  ->
      match uu___214_1419 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1421 -> s
and binder_to_string':
  Prims.bool ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) -> Prims.string
  =
  fun is_arrow  ->
    fun b  ->
      let uu____1427 = b in
      match uu____1427 with
      | (a,imp) ->
          let uu____1432 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____1432
          then
            let uu____1433 = term_to_string a.FStar_Syntax_Syntax.sort in
            Prims.strcat "_:" uu____1433
          else
            (let uu____1435 =
               (Prims.op_Negation is_arrow) &&
                 (let uu____1436 = FStar_Options.print_bound_var_types () in
                  Prims.op_Negation uu____1436) in
             if uu____1435
             then
               let uu____1437 = nm_to_string a in
               imp_to_string uu____1437 imp
             else
               (let uu____1439 =
                  let uu____1440 = nm_to_string a in
                  let uu____1441 =
                    let uu____1442 =
                      term_to_string a.FStar_Syntax_Syntax.sort in
                    Prims.strcat ":" uu____1442 in
                  Prims.strcat uu____1440 uu____1441 in
                imp_to_string uu____1439 imp))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1450 = FStar_Options.print_implicits () in
        if uu____1450 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1452 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1452 (FStar_String.concat sep)
      else
        (let uu____1459 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1459 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier Prims.option)
    -> Prims.string
  =
  fun uu___215_1463  ->
    match uu___215_1463 with
    | (a,imp) ->
        let uu____1471 = term_to_string a in imp_to_string uu____1471 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1474 = FStar_Options.print_implicits () in
      if uu____1474 then args else filter_imp args in
    let uu____1478 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1478 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1487) ->
        let uu____1494 =
          let uu____1495 = FStar_Syntax_Subst.compress t in
          uu____1495.FStar_Syntax_Syntax.n in
        (match uu____1494 with
         | FStar_Syntax_Syntax.Tm_type uu____1498 when
             let uu____1499 = FStar_Options.print_implicits () in
             Prims.op_Negation uu____1499 -> term_to_string t
         | uu____1500 ->
             let uu____1501 = term_to_string t in
             FStar_Util.format1 "Tot %s" uu____1501)
    | FStar_Syntax_Syntax.GTotal (t,uu____1503) ->
        let uu____1510 =
          let uu____1511 = FStar_Syntax_Subst.compress t in
          uu____1511.FStar_Syntax_Syntax.n in
        (match uu____1510 with
         | FStar_Syntax_Syntax.Tm_type uu____1514 when
             let uu____1515 = FStar_Options.print_implicits () in
             Prims.op_Negation uu____1515 -> term_to_string t
         | uu____1516 ->
             let uu____1517 = term_to_string t in
             FStar_Util.format1 "GTot %s" uu____1517)
    | FStar_Syntax_Syntax.Comp c1 ->
        let basic =
          let uu____1520 = FStar_Options.print_effect_args () in
          if uu____1520
          then
            let uu____1521 = sli c1.FStar_Syntax_Syntax.effect_name in
            let uu____1522 = term_to_string c1.FStar_Syntax_Syntax.result_typ in
            let uu____1523 =
              let uu____1524 =
                FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map arg_to_string) in
              FStar_All.pipe_right uu____1524 (FStar_String.concat ", ") in
            let uu____1536 =
              let uu____1537 =
                FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                  (FStar_List.map cflags_to_string) in
              FStar_All.pipe_right uu____1537 (FStar_String.concat " ") in
            FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1521
              uu____1522 uu____1523 uu____1536
          else
            (let uu____1543 =
               (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___216_1545  ->
                        match uu___216_1545 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____1546 -> false)))
                 &&
                 (let uu____1547 = FStar_Options.print_effect_args () in
                  Prims.op_Negation uu____1547) in
             if uu____1543
             then
               let uu____1548 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               FStar_Util.format1 "Tot %s" uu____1548
             else
               (let uu____1550 =
                  ((let uu____1551 = FStar_Options.print_effect_args () in
                    Prims.op_Negation uu____1551) &&
                     (let uu____1552 = FStar_Options.print_implicits () in
                      Prims.op_Negation uu____1552))
                    &&
                    (FStar_Ident.lid_equals
                       c1.FStar_Syntax_Syntax.effect_name
                       FStar_Syntax_Const.effect_ML_lid) in
                if uu____1550
                then term_to_string c1.FStar_Syntax_Syntax.result_typ
                else
                  (let uu____1554 =
                     (let uu____1555 = FStar_Options.print_effect_args () in
                      Prims.op_Negation uu____1555) &&
                       (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                          (FStar_Util.for_some
                             (fun uu___217_1557  ->
                                match uu___217_1557 with
                                | FStar_Syntax_Syntax.MLEFFECT  -> true
                                | uu____1558 -> false))) in
                   if uu____1554
                   then
                     let uu____1559 =
                       term_to_string c1.FStar_Syntax_Syntax.result_typ in
                     FStar_Util.format1 "ALL %s" uu____1559
                   else
                     (let uu____1561 = sli c1.FStar_Syntax_Syntax.effect_name in
                      let uu____1562 =
                        term_to_string c1.FStar_Syntax_Syntax.result_typ in
                      FStar_Util.format2 "%s (%s)" uu____1561 uu____1562)))) in
        let dec =
          let uu____1564 =
            FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
              (FStar_List.collect
                 (fun uu___218_1568  ->
                    match uu___218_1568 with
                    | FStar_Syntax_Syntax.DECREASES e ->
                        let uu____1573 =
                          let uu____1574 = term_to_string e in
                          FStar_Util.format1 " (decreases %s)" uu____1574 in
                        [uu____1573]
                    | uu____1575 -> [])) in
          FStar_All.pipe_right uu____1564 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1578 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1587 = FStar_Options.print_universes () in
    if uu____1587 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun uu____1591  ->
    match uu____1591 with
    | (us,t) ->
        let uu____1596 =
          let uu____1597 = univ_names_to_string us in
          FStar_All.pipe_left enclose_universes uu____1597 in
        let uu____1598 = term_to_string t in
        FStar_Util.format2 "%s%s" uu____1596 uu____1598
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  ->
      let actions_to_string actions =
        let uu____1611 =
          FStar_All.pipe_right actions
            (FStar_List.map
               (fun a  ->
                  let uu____1616 = sli a.FStar_Syntax_Syntax.action_name in
                  let uu____1617 =
                    binders_to_string " " a.FStar_Syntax_Syntax.action_params in
                  let uu____1618 =
                    let uu____1619 =
                      univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
                    FStar_All.pipe_left enclose_universes uu____1619 in
                  let uu____1620 =
                    term_to_string a.FStar_Syntax_Syntax.action_typ in
                  let uu____1621 =
                    term_to_string a.FStar_Syntax_Syntax.action_defn in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1616
                    uu____1617 uu____1618 uu____1620 uu____1621)) in
        FStar_All.pipe_right uu____1611 (FStar_String.concat ",\n\t") in
      let uu____1623 =
        let uu____1625 =
          let uu____1627 = lid_to_string ed.FStar_Syntax_Syntax.mname in
          let uu____1628 =
            let uu____1630 =
              let uu____1631 =
                univ_names_to_string ed.FStar_Syntax_Syntax.univs in
              FStar_All.pipe_left enclose_universes uu____1631 in
            let uu____1632 =
              let uu____1634 =
                binders_to_string " " ed.FStar_Syntax_Syntax.binders in
              let uu____1635 =
                let uu____1637 =
                  term_to_string ed.FStar_Syntax_Syntax.signature in
                let uu____1638 =
                  let uu____1640 =
                    tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                  let uu____1641 =
                    let uu____1643 =
                      tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                    let uu____1644 =
                      let uu____1646 =
                        tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else in
                      let uu____1647 =
                        let uu____1649 =
                          tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp in
                        let uu____1650 =
                          let uu____1652 =
                            tscheme_to_string ed.FStar_Syntax_Syntax.stronger in
                          let uu____1653 =
                            let uu____1655 =
                              tscheme_to_string
                                ed.FStar_Syntax_Syntax.close_wp in
                            let uu____1656 =
                              let uu____1658 =
                                tscheme_to_string
                                  ed.FStar_Syntax_Syntax.assert_p in
                              let uu____1659 =
                                let uu____1661 =
                                  tscheme_to_string
                                    ed.FStar_Syntax_Syntax.assume_p in
                                let uu____1662 =
                                  let uu____1664 =
                                    tscheme_to_string
                                      ed.FStar_Syntax_Syntax.null_wp in
                                  let uu____1665 =
                                    let uu____1667 =
                                      tscheme_to_string
                                        ed.FStar_Syntax_Syntax.trivial in
                                    let uu____1668 =
                                      let uu____1670 =
                                        term_to_string
                                          ed.FStar_Syntax_Syntax.repr in
                                      let uu____1671 =
                                        let uu____1673 =
                                          tscheme_to_string
                                            ed.FStar_Syntax_Syntax.bind_repr in
                                        let uu____1674 =
                                          let uu____1676 =
                                            tscheme_to_string
                                              ed.FStar_Syntax_Syntax.return_repr in
                                          let uu____1677 =
                                            let uu____1679 =
                                              actions_to_string
                                                ed.FStar_Syntax_Syntax.actions in
                                            [uu____1679] in
                                          uu____1676 :: uu____1677 in
                                        uu____1673 :: uu____1674 in
                                      uu____1670 :: uu____1671 in
                                    uu____1667 :: uu____1668 in
                                  uu____1664 :: uu____1665 in
                                uu____1661 :: uu____1662 in
                              uu____1658 :: uu____1659 in
                            uu____1655 :: uu____1656 in
                          uu____1652 :: uu____1653 in
                        uu____1649 :: uu____1650 in
                      uu____1646 :: uu____1647 in
                    uu____1643 :: uu____1644 in
                  uu____1640 :: uu____1641 in
                uu____1637 :: uu____1638 in
              uu____1634 :: uu____1635 in
            uu____1630 :: uu____1632 in
          uu____1627 :: uu____1628 in
        (if for_free then "_for_free " else "") :: uu____1625 in
      FStar_Util.format
        "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
        uu____1623
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
        "#light \"off\""
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (None
        )) -> "#reset-options"
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions (Some
        s)) -> FStar_Util.format1 "#reset-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
        FStar_Util.format1 "#set-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,univs1,tps,k,uu____1690,uu____1691) ->
        let uu____1696 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
        let uu____1697 = binders_to_string " " tps in
        let uu____1698 = term_to_string k in
        FStar_Util.format4 "%stype %s %s : %s" uu____1696 lid.FStar_Ident.str
          uu____1697 uu____1698
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,univs1,t,uu____1702,uu____1703,uu____1704) ->
        let uu____1707 = FStar_Options.print_universes () in
        if uu____1707
        then
          let uu____1708 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          (match uu____1708 with
           | (univs2,t1) ->
               let uu____1713 = univ_names_to_string univs2 in
               let uu____1714 = term_to_string t1 in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____1713
                 lid.FStar_Ident.str uu____1714)
        else
          (let uu____1716 = term_to_string t in
           FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
             uu____1716)
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
        let uu____1720 = FStar_Syntax_Subst.open_univ_vars univs1 t in
        (match uu____1720 with
         | (univs2,t1) ->
             let uu____1725 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let uu____1726 =
               let uu____1727 = FStar_Options.print_universes () in
               if uu____1727
               then
                 let uu____1728 = univ_names_to_string univs2 in
                 FStar_Util.format1 "<%s>" uu____1728
               else "" in
             let uu____1730 = term_to_string t1 in
             FStar_Util.format4 "%sval %s %s : %s" uu____1725
               lid.FStar_Ident.str uu____1726 uu____1730)
    | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
        let uu____1733 = term_to_string f in
        FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1733
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____1735,uu____1736) ->
        lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
    | FStar_Syntax_Syntax.Sig_main e ->
        let uu____1742 = term_to_string e in
        FStar_Util.format1 "let _ = %s" uu____1742
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1744) ->
        let uu____1749 = FStar_List.map sigelt_to_string ses in
        FStar_All.pipe_right uu____1749 (FStar_String.concat "\n")
    | FStar_Syntax_Syntax.Sig_new_effect ed -> eff_decl_to_string false ed
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        eff_decl_to_string true ed
    | FStar_Syntax_Syntax.Sig_sub_effect se ->
        let lift_wp =
          match ((se.FStar_Syntax_Syntax.lift_wp),
                  (se.FStar_Syntax_Syntax.lift))
          with
          | (None ,None ) -> failwith "impossible"
          | (Some lift_wp,uu____1761) -> lift_wp
          | (uu____1765,Some lift) -> lift in
        let uu____1770 =
          FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp)
            (Prims.snd lift_wp) in
        (match uu____1770 with
         | (us,t) ->
             let uu____1777 = lid_to_string se.FStar_Syntax_Syntax.source in
             let uu____1778 = lid_to_string se.FStar_Syntax_Syntax.target in
             let uu____1779 = univ_names_to_string us in
             let uu____1780 = term_to_string t in
             FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1777
               uu____1778 uu____1779 uu____1780)
    | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
        let uu____1788 = FStar_Options.print_universes () in
        if uu____1788
        then
          let uu____1789 =
            let uu____1792 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (tps, c)))
                None FStar_Range.dummyRange in
            FStar_Syntax_Subst.open_univ_vars univs1 uu____1792 in
          (match uu____1789 with
           | (univs2,t) ->
               let uu____1803 =
                 let uu____1811 =
                   let uu____1812 = FStar_Syntax_Subst.compress t in
                   uu____1812.FStar_Syntax_Syntax.n in
                 match uu____1811 with
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                 | uu____1839 -> failwith "impossible" in
               (match uu____1803 with
                | (tps1,c1) ->
                    let uu____1859 = sli l in
                    let uu____1860 = univ_names_to_string univs2 in
                    let uu____1861 = binders_to_string " " tps1 in
                    let uu____1862 = comp_to_string c1 in
                    FStar_Util.format4 "effect %s<%s> %s = %s" uu____1859
                      uu____1860 uu____1861 uu____1862))
        else
          (let uu____1864 = sli l in
           let uu____1865 = binders_to_string " " tps in
           let uu____1866 = comp_to_string c in
           FStar_Util.format3 "effect %s %s = %s" uu____1864 uu____1865
             uu____1866)
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1873 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1873 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1877,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1879;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1881;
                       FStar_Syntax_Syntax.lbdef = uu____1882;_}::[]),uu____1883,uu____1884)
        ->
        let uu____1900 = lbname_to_string lb in
        let uu____1901 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1900 uu____1901
    | uu____1902 ->
        let uu____1903 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1903 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1912 = sli m.FStar_Syntax_Syntax.name in
    let uu____1913 =
      let uu____1914 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1914 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1912 uu____1913
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___219_1919  ->
    match uu___219_1919 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1922 = FStar_Util.string_of_int i in
        let uu____1923 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1922 uu____1923
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1926 = bv_to_string x in
        let uu____1927 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1926 uu____1927
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1934 = bv_to_string x in
        let uu____1935 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1934 uu____1935
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1938 = FStar_Util.string_of_int i in
        let uu____1939 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1938 uu____1939
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1942 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1942
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1946 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1946 (FStar_String.concat "; ")
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
       (let uu____1996 = f x in
        FStar_Util.string_builder_append strb uu____1996);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2000 = f x1 in
             FStar_Util.string_builder_append strb uu____2000)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2029 = f x in
        FStar_Util.string_builder_append strb uu____2029);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2033 = f x1 in
             FStar_Util.string_builder_append strb uu____2033)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)