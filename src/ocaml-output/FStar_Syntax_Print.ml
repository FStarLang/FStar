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
          let uu____284 =
            let uu____289 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____289 in
          (match uu____284 with
           | Some xs ->
               let uu____303 =
                 let uu____307 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____307 :: xs in
               Some uu____303
           | None  -> None)
        else None
    | uu____327 ->
        let uu____328 = is_lex_top e in if uu____328 then Some [] else None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____364 = f hd1 in if uu____364 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident* Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____378 = find (fun p  -> FStar_Ident.lid_equals x (fst p)) xs in
      snd uu____378
let infix_prim_op_to_string e =
  let uu____397 = get_lid e in find_lid uu____397 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____409 = get_lid e in find_lid uu____409 unary_prim_ops
let quant_to_string t =
  let uu____421 = get_lid t in find_lid uu____421 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____429) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____432 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____437) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____447 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____447
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___210_450  ->
    match uu___210_450 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____461 = db_to_string x in Prims.strcat "Tm_bvar: " uu____461
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____463 = nm_to_string x in Prims.strcat "Tm_name: " uu____463
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____465 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____465
    | FStar_Syntax_Syntax.Tm_uinst uu____470 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____475 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____476 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____477 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____492 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____500 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____505 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____515 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____531 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____549 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____557 -> "Tm_uvar"
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
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____635 = FStar_Options.hide_uvar_nums () in
    if uu____635
    then "?"
    else
      (let uu____637 =
         let uu____638 = FStar_Syntax_Unionfind.univ_uvar_id u in
         FStar_All.pipe_right uu____638 FStar_Util.string_of_int in
       Prims.strcat "?" uu____637)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____648 = FStar_Syntax_Subst.compress_univ u in
      match uu____648 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____654 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____659 =
      let uu____660 = FStar_Options.ugly () in Prims.op_Negation uu____660 in
    if uu____659
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____664 = FStar_Syntax_Subst.compress_univ u in
       match uu____664 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____670 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____670
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____672 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____672 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____681 = univ_to_string u2 in
                let uu____682 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____681 uu____682)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____685 =
             let uu____686 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____686 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____685
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____694 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____694 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____702 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____702 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___211_708  ->
    match uu___211_708 with
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
        let uu____710 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____710
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____713 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____713 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____720 =
          let uu____721 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____721 in
        let uu____723 =
          let uu____724 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____724 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____720 uu____723
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____735 =
          let uu____736 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____736 in
        let uu____738 =
          let uu____739 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____739 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____735 uu____738
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____745 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____745
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
    | uu____752 ->
        let uu____754 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____754 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____764 ->
        let uu____766 = quals_to_string quals in Prims.strcat uu____766 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____814 =
      let uu____815 = FStar_Options.ugly () in Prims.op_Negation uu____815 in
    if uu____814
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____821 = FStar_Options.print_implicits () in
         if uu____821 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____823 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____844,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____871 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____887 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____895  ->
                                 match uu____895 with
                                 | (t1,uu____899) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____887
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____871 (FStar_String.concat "\\/") in
           let uu____902 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____902
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____914 = tag_of_term t in
           let uu____915 = sli m in
           let uu____916 = term_to_string t' in
           let uu____917 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____914 uu____915
             uu____916 uu____917
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____930 = tag_of_term t in
           let uu____931 = term_to_string t' in
           let uu____932 = sli m0 in
           let uu____933 = sli m1 in
           let uu____934 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____930
             uu____931 uu____932 uu____933 uu____934
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____943 = FStar_Range.string_of_range r in
           let uu____944 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____943
             uu____944
       | FStar_Syntax_Syntax.Tm_meta (t,uu____946) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____955) -> uvar_to_string u
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
    let uu____1237 =
      let uu____1238 = FStar_Options.ugly () in Prims.op_Negation uu____1238 in
    if uu____1237
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1254 = fv_to_string l in
           let uu____1255 =
             let uu____1256 =
               FStar_List.map
                 (fun uu____1260  ->
                    match uu____1260 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1256 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1254 uu____1255
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1269) ->
           let uu____1274 = FStar_Options.print_bound_var_types () in
           if uu____1274
           then
             let uu____1275 = bv_to_string x1 in
             let uu____1276 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1275 uu____1276
           else
             (let uu____1278 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1278)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1280 = FStar_Options.print_bound_var_types () in
           if uu____1280
           then
             let uu____1281 = bv_to_string x1 in
             let uu____1282 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1281 uu____1282
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1286 = FStar_Options.print_real_names () in
           if uu____1286
           then
             let uu____1287 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1287
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1299 = FStar_Options.print_universes () in
        if uu____1299
        then
          let uu____1303 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1309 =
                      let uu____1312 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1312 in
                    match uu____1309 with
                    | (us,td) ->
                        let uu____1315 =
                          let uu____1322 =
                            let uu____1323 = FStar_Syntax_Subst.compress td in
                            uu____1323.FStar_Syntax_Syntax.n in
                          match uu____1322 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1332,(t,uu____1334)::(d,uu____1336)::[])
                              -> (t, d)
                          | uu____1370 -> failwith "Impossibe" in
                        (match uu____1315 with
                         | (t,d) ->
                             let uu___218_1387 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___218_1387.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___218_1387.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1303)
        else lbs in
      let uu____1391 = quals_to_string' quals in
      let uu____1392 =
        let uu____1393 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1399 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1400 =
                    let uu____1401 = FStar_Options.print_universes () in
                    if uu____1401
                    then
                      let uu____1402 =
                        let uu____1403 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1403 ">" in
                      Prims.strcat "<" uu____1402
                    else "" in
                  let uu____1405 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1406 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1399 uu____1400
                    uu____1405 uu____1406)) in
        FStar_Util.concat_l "\n and " uu____1393 in
      FStar_Util.format3 "%slet %s %s" uu____1391
        (if fst lbs1 then "rec" else "") uu____1392
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1412 = FStar_Options.print_effect_args () in
    if uu____1412
    then
      let uu____1413 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1413
    else
      (let uu____1415 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1416 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1415 uu____1416)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___212_1418  ->
      match uu___212_1418 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1420 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1424 =
        let uu____1425 = FStar_Options.ugly () in
        Prims.op_Negation uu____1425 in
      if uu____1424
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1429 = b in
         match uu____1429 with
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
                   imp_to_string uu____1439 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1448 = FStar_Options.print_implicits () in
        if uu____1448 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1450 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1450 (FStar_String.concat sep)
      else
        (let uu____1455 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1455 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___213_1459  ->
    match uu___213_1459 with
    | (a,imp) ->
        let uu____1467 = term_to_string a in imp_to_string uu____1467 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1470 = FStar_Options.print_implicits () in
      if uu____1470 then args else filter_imp args in
    let uu____1474 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1474 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1482 =
      let uu____1483 = FStar_Options.ugly () in Prims.op_Negation uu____1483 in
    if uu____1482
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1488) ->
           let uu____1495 =
             let uu____1496 = FStar_Syntax_Subst.compress t in
             uu____1496.FStar_Syntax_Syntax.n in
           (match uu____1495 with
            | FStar_Syntax_Syntax.Tm_type uu____1499 when
                let uu____1500 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1500 -> term_to_string t
            | uu____1501 ->
                let uu____1502 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____1502)
       | FStar_Syntax_Syntax.GTotal (t,uu____1504) ->
           let uu____1511 =
             let uu____1512 = FStar_Syntax_Subst.compress t in
             uu____1512.FStar_Syntax_Syntax.n in
           (match uu____1511 with
            | FStar_Syntax_Syntax.Tm_type uu____1515 when
                let uu____1516 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1516 -> term_to_string t
            | uu____1517 ->
                let uu____1518 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____1518)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1521 = FStar_Options.print_effect_args () in
             if uu____1521
             then
               let uu____1522 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1523 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1524 =
                 let uu____1525 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1525 (FStar_String.concat ", ") in
               let uu____1537 =
                 let uu____1538 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1538 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1522
                 uu____1523 uu____1524 uu____1537
             else
               (let uu____1544 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___214_1546  ->
                           match uu___214_1546 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1547 -> false)))
                    &&
                    (let uu____1548 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1548) in
                if uu____1544
                then
                  let uu____1549 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1549
                else
                  (let uu____1551 =
                     ((let uu____1552 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1552) &&
                        (let uu____1553 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1553))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1551
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1555 =
                        (let uu____1556 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1556) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___215_1558  ->
                                   match uu___215_1558 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1559 -> false))) in
                      if uu____1555
                      then
                        let uu____1560 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1560
                      else
                        (let uu____1562 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1563 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1562 uu____1563)))) in
           let dec =
             let uu____1565 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___216_1569  ->
                       match uu___216_1569 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1574 =
                             let uu____1575 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1575 in
                           [uu____1574]
                       | uu____1576 -> [])) in
             FStar_All.pipe_right uu____1565 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1579 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1588 = FStar_Options.print_universes () in
    if uu____1588 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1593 =
      let uu____1594 = FStar_Options.ugly () in Prims.op_Negation uu____1594 in
    if uu____1593
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1598 = s in
       match uu____1598 with
       | (us,t) ->
           let uu____1603 =
             let uu____1604 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1604 in
           let uu____1605 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1603 uu____1605)
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
          let uu____1620 =
            let uu____1621 = FStar_Options.ugly () in
            Prims.op_Negation uu____1621 in
          if uu____1620
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1631 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____1636 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____1637 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____1638 =
                           let uu____1639 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____1639 in
                         let uu____1640 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____1641 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____1636
                           uu____1637 uu____1638 uu____1640 uu____1641)) in
               FStar_All.pipe_right uu____1631 (FStar_String.concat ",\n\t") in
             let uu____1643 =
               let uu____1645 =
                 let uu____1647 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1648 =
                   let uu____1650 =
                     let uu____1651 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1651 in
                   let uu____1652 =
                     let uu____1654 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1655 =
                       let uu____1657 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1658 =
                         let uu____1660 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1661 =
                           let uu____1663 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1664 =
                             let uu____1666 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1667 =
                               let uu____1669 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1670 =
                                 let uu____1672 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1673 =
                                   let uu____1675 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1676 =
                                     let uu____1678 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1679 =
                                       let uu____1681 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1682 =
                                         let uu____1684 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1685 =
                                           let uu____1687 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1688 =
                                             let uu____1690 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1691 =
                                               let uu____1693 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1694 =
                                                 let uu____1696 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1697 =
                                                   let uu____1699 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1699] in
                                                 uu____1696 :: uu____1697 in
                                               uu____1693 :: uu____1694 in
                                             uu____1690 :: uu____1691 in
                                           uu____1687 :: uu____1688 in
                                         uu____1684 :: uu____1685 in
                                       uu____1681 :: uu____1682 in
                                     uu____1678 :: uu____1679 in
                                   uu____1675 :: uu____1676 in
                                 uu____1672 :: uu____1673 in
                               uu____1669 :: uu____1670 in
                             uu____1666 :: uu____1667 in
                           uu____1663 :: uu____1664 in
                         uu____1660 :: uu____1661 in
                       uu____1657 :: uu____1658 in
                     uu____1654 :: uu____1655 in
                   uu____1650 :: uu____1652 in
                 uu____1647 :: uu____1648 in
               (if for_free then "_for_free " else "") :: uu____1645 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1643)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1710 =
      let uu____1711 = FStar_Options.ugly () in Prims.op_Negation uu____1711 in
    if uu____1710
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1716 -> ""
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
           (lid,univs1,tps,k,uu____1725,uu____1726) ->
           let uu____1731 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1732 = binders_to_string " " tps in
           let uu____1733 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1731
             lid.FStar_Ident.str uu____1732 uu____1733
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1737,uu____1738,uu____1739) ->
           let uu____1742 = FStar_Options.print_universes () in
           if uu____1742
           then
             let uu____1743 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1743 with
              | (univs2,t1) ->
                  let uu____1748 = univ_names_to_string univs2 in
                  let uu____1749 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1748
                    lid.FStar_Ident.str uu____1749)
           else
             (let uu____1751 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1751)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1755 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1755 with
            | (univs2,t1) ->
                let uu____1760 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1761 =
                  let uu____1762 = FStar_Options.print_universes () in
                  if uu____1762
                  then
                    let uu____1763 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1763
                  else "" in
                let uu____1765 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1760
                  lid.FStar_Ident.str uu____1761 uu____1765)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____1768 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1768
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1770,uu____1771) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1777 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1777
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1779) ->
           let uu____1784 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1784 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1796) -> lift_wp
             | (uu____1800,Some lift) -> lift in
           let uu____1805 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1805 with
            | (us,t) ->
                let uu____1812 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1813 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1814 = univ_names_to_string us in
                let uu____1815 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1812
                  uu____1813 uu____1814 uu____1815)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1823 = FStar_Options.print_universes () in
           if uu____1823
           then
             let uu____1824 =
               let uu____1827 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1827 in
             (match uu____1824 with
              | (univs2,t) ->
                  let uu____1838 =
                    let uu____1846 =
                      let uu____1847 = FStar_Syntax_Subst.compress t in
                      uu____1847.FStar_Syntax_Syntax.n in
                    match uu____1846 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1874 -> failwith "impossible" in
                  (match uu____1838 with
                   | (tps1,c1) ->
                       let uu____1894 = sli l in
                       let uu____1895 = univ_names_to_string univs2 in
                       let uu____1896 = binders_to_string " " tps1 in
                       let uu____1897 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1894
                         uu____1895 uu____1896 uu____1897))
           else
             (let uu____1899 = sli l in
              let uu____1900 = binders_to_string " " tps in
              let uu____1901 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1899 uu____1900
                uu____1901))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1908 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1908 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1912,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1914;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1916;
                       FStar_Syntax_Syntax.lbdef = uu____1917;_}::[]),uu____1918,uu____1919)
        ->
        let uu____1935 = lbname_to_string lb in
        let uu____1936 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1935 uu____1936
    | uu____1937 ->
        let uu____1938 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1938 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1947 = sli m.FStar_Syntax_Syntax.name in
    let uu____1948 =
      let uu____1949 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1949 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1947 uu____1948
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___217_1954  ->
    match uu___217_1954 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1957 = FStar_Util.string_of_int i in
        let uu____1958 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1957 uu____1958
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1961 = bv_to_string x in
        let uu____1962 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1961 uu____1962
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1969 = bv_to_string x in
        let uu____1970 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1969 uu____1970
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1973 = FStar_Util.string_of_int i in
        let uu____1974 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1973 uu____1974
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1977 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1977
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1981 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1981 (FStar_String.concat "; ")
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
       (let uu____2031 = f x in
        FStar_Util.string_builder_append strb uu____2031);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2035 = f x1 in
             FStar_Util.string_builder_append strb uu____2035)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2064 = f x in
        FStar_Util.string_builder_append strb uu____2064);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2068 = f x1 in
             FStar_Util.string_builder_append strb uu____2068)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)