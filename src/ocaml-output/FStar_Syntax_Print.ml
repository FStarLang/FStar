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
    let uu____15 =
      let uu____16 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____16 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____15
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____20 = FStar_Options.print_real_names () in
    if uu____20
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____25 =
      let uu____26 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____26 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____25
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
  | uu____118 -> failwith "get_lid"
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
let is_inr uu___198_165 =
  match uu___198_165 with
  | FStar_Util.Inl uu____168 -> false
  | FStar_Util.Inr uu____169 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___199_203  ->
          match uu___199_203 with
          | (uu____207,Some (FStar_Syntax_Syntax.Implicit uu____208)) ->
              false
          | uu____210 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list option
  =
  fun e  ->
    let uu____221 =
      let uu____222 = FStar_Syntax_Subst.compress e in
      uu____222.FStar_Syntax_Syntax.n in
    match uu____221 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives.fst args1 in
        let uu____268 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____268
        then
          let uu____277 =
            let uu____282 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____282 in
          (match uu____277 with
           | Some xs ->
               let uu____296 =
                 let uu____300 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____300 :: xs in
               Some uu____296
           | None  -> None)
        else None
    | uu____320 ->
        let uu____321 = is_lex_top e in if uu____321 then Some [] else None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____357 = f hd1 in if uu____357 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident* Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____371 = find (fun p  -> FStar_Ident.lid_equals x (fst p)) xs in
      snd uu____371
let infix_prim_op_to_string e =
  let uu____391 = get_lid e in find_lid uu____391 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____403 = get_lid e in find_lid uu____403 unary_prim_ops
let quant_to_string t =
  let uu____415 = get_lid t in find_lid uu____415 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____423) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____426 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____431) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____441 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____441
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___200_444  ->
    match uu___200_444 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____451 = db_to_string x in Prims.strcat "Tm_bvar: " uu____451
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____453 = nm_to_string x in Prims.strcat "Tm_name: " uu____453
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____455 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____455
    | FStar_Syntax_Syntax.Tm_uinst uu____456 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____461 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____462 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____463 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____478 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____486 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____491 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____501 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____516 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____534 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____542 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____553,m) ->
        let uu____591 = FStar_ST.read m in
        (match uu____591 with
         | None  -> "Tm_delayed"
         | Some uu____602 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____607 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____615 = FStar_Options.hide_uvar_nums () in
    if uu____615
    then "?"
    else
      (let uu____617 =
         let uu____618 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____618 FStar_Util.string_of_int in
       Prims.strcat "?" uu____617)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____622 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____623 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____622 uu____623
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____627 = FStar_Options.hide_uvar_nums () in
    if uu____627
    then "?"
    else
      (let uu____629 =
         let uu____630 =
           let uu____631 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____631 FStar_Util.string_of_int in
         let uu____632 =
           let uu____633 = version_to_string (snd u) in
           Prims.strcat ":" uu____633 in
         Prims.strcat uu____630 uu____632 in
       Prims.strcat "?" uu____629)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
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
    let uu____656 =
      let uu____657 = FStar_Options.ugly () in Prims.op_Negation uu____657 in
    if uu____656
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____661 = FStar_Syntax_Subst.compress_univ u in
       match uu____661 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____669 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____669
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____671 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____671 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____680 = univ_to_string u2 in
                let uu____681 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____680 uu____681)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____684 =
             let uu____685 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____685 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____684
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____693 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____693 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____701 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____701 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___201_708  ->
    match uu___201_708 with
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
                       let uu____889 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____900  ->
                                 match uu____900 with
                                 | (t1,uu____904) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____889
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____871 (FStar_String.concat "\\/") in
           let uu____907 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____907
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____919 = tag_of_term t in
           let uu____920 = sli m in
           let uu____921 = term_to_string t' in
           let uu____922 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____919 uu____920
             uu____921 uu____922
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____935 = tag_of_term t in
           let uu____936 = term_to_string t' in
           let uu____937 = sli m0 in
           let uu____938 = sli m1 in
           let uu____939 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____935
             uu____936 uu____937 uu____938 uu____939
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____948 = FStar_Range.string_of_range r in
           let uu____949 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____948
             uu____949
       | FStar_Syntax_Syntax.Tm_meta (t,uu____951) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____957 = db_to_string x3 in
           let uu____958 =
             let uu____959 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____959 in
           Prims.strcat uu____957 uu____958
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____963) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____982 = FStar_Options.print_universes () in
           if uu____982
           then
             let uu____983 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____983
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____997 = binders_to_string " -> " bs in
           let uu____998 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____997 uu____998
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some (FStar_Util.Inl l) when FStar_Options.print_implicits ()
                ->
                let uu____1033 = binders_to_string " " bs in
                let uu____1034 = term_to_string t2 in
                let uu____1035 =
                  let uu____1036 = l.FStar_Syntax_Syntax.comp () in
                  FStar_All.pipe_left comp_to_string uu____1036 in
                FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1033
                  uu____1034 uu____1035
            | Some (FStar_Util.Inr (l,flags)) when
                FStar_Options.print_implicits () ->
                let uu____1049 = binders_to_string " " bs in
                let uu____1050 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____1049 uu____1050 l.FStar_Ident.str
            | uu____1051 ->
                let uu____1058 = binders_to_string " " bs in
                let uu____1059 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1058 uu____1059)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1066 = bv_to_string xt in
           let uu____1067 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1070 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1066 uu____1067 uu____1070
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1089 = term_to_string t in
           let uu____1090 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1089 uu____1090
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1103 = lbs_to_string [] lbs in
           let uu____1104 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1103 uu____1104
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1152 =
                   let uu____1153 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1153
                     (FStar_Util.dflt "default") in
                 let uu____1156 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1152 uu____1156
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1172 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1172 in
           let uu____1173 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1173 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1200 = term_to_string head1 in
           let uu____1201 =
             let uu____1202 =
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
             FStar_Util.concat_l "\n\t|" uu____1202 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1200 uu____1201
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
           let uu____1268 = fv_to_string l in
           let uu____1269 =
             let uu____1270 =
               FStar_List.map
                 (fun uu____1278  ->
                    match uu____1278 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1270 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1268 uu____1269
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1287) ->
           let uu____1292 = FStar_Options.print_bound_var_types () in
           if uu____1292
           then
             let uu____1293 = bv_to_string x1 in
             let uu____1294 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1293 uu____1294
           else
             (let uu____1296 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1296)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1298 = FStar_Options.print_bound_var_types () in
           if uu____1298
           then
             let uu____1299 = bv_to_string x1 in
             let uu____1300 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1299 uu____1300
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1304 = FStar_Options.print_real_names () in
           if uu____1304
           then
             let uu____1305 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1305
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1317 = FStar_Options.print_universes () in
        if uu____1317
        then
          let uu____1321 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1335 =
                      let uu____1338 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1338 in
                    match uu____1335 with
                    | (us,td) ->
                        let uu____1341 =
                          let uu____1348 =
                            let uu____1349 = FStar_Syntax_Subst.compress td in
                            uu____1349.FStar_Syntax_Syntax.n in
                          match uu____1348 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1358,(t,uu____1360)::(d,uu____1362)::[])
                              -> (t, d)
                          | uu____1396 -> failwith "Impossibe" in
                        (match uu____1341 with
                         | (t,d) ->
                             let uu___208_1413 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___208_1413.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___208_1413.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1321)
        else lbs in
      let uu____1417 = quals_to_string' quals in
      let uu____1418 =
        let uu____1419 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1430 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1431 =
                    let uu____1432 = FStar_Options.print_universes () in
                    if uu____1432
                    then
                      let uu____1433 =
                        let uu____1434 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1434 ">" in
                      Prims.strcat "<" uu____1433
                    else "" in
                  let uu____1436 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1437 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1430 uu____1431
                    uu____1436 uu____1437)) in
        FStar_Util.concat_l "\n and " uu____1419 in
      FStar_Util.format3 "%slet %s %s" uu____1417
        (if fst lbs1 then "rec" else "") uu____1418
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1443 = FStar_Options.print_effect_args () in
    if uu____1443
    then
      let uu____1444 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1444
    else
      (let uu____1446 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1447 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1446 uu____1447)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___202_1449  ->
      match uu___202_1449 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1451 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1455 =
        let uu____1456 = FStar_Options.ugly () in
        Prims.op_Negation uu____1456 in
      if uu____1455
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1460 = b in
         match uu____1460 with
         | (a,imp) ->
             let uu____1463 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1463
             then
               let uu____1464 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1464
             else
               (let uu____1466 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1468 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1468) in
                if uu____1466
                then
                  let uu____1469 = nm_to_string a in
                  imp_to_string uu____1469 imp
                else
                  (let uu____1471 =
                     let uu____1472 = nm_to_string a in
                     let uu____1473 =
                       let uu____1474 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1474 in
                     Prims.strcat uu____1472 uu____1473 in
                   imp_to_string uu____1471 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1480 = FStar_Options.print_implicits () in
        if uu____1480 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1482 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1482 (FStar_String.concat sep)
      else
        (let uu____1487 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1487 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___203_1491  ->
    match uu___203_1491 with
    | (a,imp) ->
        let uu____1499 = term_to_string a in imp_to_string uu____1499 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1502 = FStar_Options.print_implicits () in
      if uu____1502 then args else filter_imp args in
    let uu____1506 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1506 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1514 =
      let uu____1515 = FStar_Options.ugly () in Prims.op_Negation uu____1515 in
    if uu____1514
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1527 =
             let uu____1528 = FStar_Syntax_Subst.compress t in
             uu____1528.FStar_Syntax_Syntax.n in
           (match uu____1527 with
            | FStar_Syntax_Syntax.Tm_type uu____1531 when
                let uu____1532 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1532 -> term_to_string t
            | uu____1533 ->
                (match uopt with
                 | Some u when FStar_Options.print_universes () ->
                     let uu____1535 = univ_to_string u in
                     let uu____1536 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1535 uu____1536
                 | uu____1537 ->
                     let uu____1539 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1539))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1548 =
             let uu____1549 = FStar_Syntax_Subst.compress t in
             uu____1549.FStar_Syntax_Syntax.n in
           (match uu____1548 with
            | FStar_Syntax_Syntax.Tm_type uu____1552 when
                let uu____1553 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1553 -> term_to_string t
            | uu____1554 ->
                (match uopt with
                 | Some u when FStar_Options.print_universes () ->
                     let uu____1556 = univ_to_string u in
                     let uu____1557 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1556 uu____1557
                 | uu____1558 ->
                     let uu____1560 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1560))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1563 = FStar_Options.print_effect_args () in
             if uu____1563
             then
               let uu____1564 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1565 =
                 let uu____1566 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1566 (FStar_String.concat ", ") in
               let uu____1570 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1571 =
                 let uu____1572 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1572 (FStar_String.concat ", ") in
               let uu____1584 =
                 let uu____1585 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1585 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1564
                 uu____1565 uu____1570 uu____1571 uu____1584
             else
               (let uu____1591 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___204_1594  ->
                           match uu___204_1594 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1595 -> false)))
                    &&
                    (let uu____1597 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1597) in
                if uu____1591
                then
                  let uu____1598 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1598
                else
                  (let uu____1600 =
                     ((let uu____1603 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1603) &&
                        (let uu____1605 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1605))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1600
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1607 =
                        (let uu____1610 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1610) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___205_1613  ->
                                   match uu___205_1613 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1614 -> false))) in
                      if uu____1607
                      then
                        let uu____1615 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1615
                      else
                        (let uu____1617 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1618 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1617 uu____1618)))) in
           let dec =
             let uu____1620 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___206_1627  ->
                       match uu___206_1627 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1632 =
                             let uu____1633 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1633 in
                           [uu____1632]
                       | uu____1634 -> [])) in
             FStar_All.pipe_right uu____1620 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1637 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1646 = FStar_Options.print_universes () in
    if uu____1646 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1651 =
      let uu____1652 = FStar_Options.ugly () in Prims.op_Negation uu____1652 in
    if uu____1651
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1656 = s in
       match uu____1656 with
       | (us,t) ->
           let uu____1661 =
             let uu____1662 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1662 in
           let uu____1663 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1661 uu____1663)
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
          let uu____1678 =
            let uu____1679 = FStar_Options.ugly () in
            Prims.op_Negation uu____1679 in
          if uu____1678
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1689 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____1700 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____1701 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____1702 =
                           let uu____1703 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____1703 in
                         let uu____1704 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____1705 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____1700
                           uu____1701 uu____1702 uu____1704 uu____1705)) in
               FStar_All.pipe_right uu____1689 (FStar_String.concat ",\n\t") in
             let uu____1707 =
               let uu____1709 =
                 let uu____1711 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1712 =
                   let uu____1714 =
                     let uu____1715 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1715 in
                   let uu____1716 =
                     let uu____1718 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1719 =
                       let uu____1721 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1722 =
                         let uu____1724 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1725 =
                           let uu____1727 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1728 =
                             let uu____1730 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1731 =
                               let uu____1733 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1734 =
                                 let uu____1736 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1737 =
                                   let uu____1739 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1740 =
                                     let uu____1742 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1743 =
                                       let uu____1745 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1746 =
                                         let uu____1748 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1749 =
                                           let uu____1751 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1752 =
                                             let uu____1754 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1755 =
                                               let uu____1757 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1758 =
                                                 let uu____1760 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1761 =
                                                   let uu____1763 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1763] in
                                                 uu____1760 :: uu____1761 in
                                               uu____1757 :: uu____1758 in
                                             uu____1754 :: uu____1755 in
                                           uu____1751 :: uu____1752 in
                                         uu____1748 :: uu____1749 in
                                       uu____1745 :: uu____1746 in
                                     uu____1742 :: uu____1743 in
                                   uu____1739 :: uu____1740 in
                                 uu____1736 :: uu____1737 in
                               uu____1733 :: uu____1734 in
                             uu____1730 :: uu____1731 in
                           uu____1727 :: uu____1728 in
                         uu____1724 :: uu____1725 in
                       uu____1721 :: uu____1722 in
                     uu____1718 :: uu____1719 in
                   uu____1714 :: uu____1716 in
                 uu____1711 :: uu____1712 in
               (if for_free then "_for_free " else "") :: uu____1709 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1707)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1774 =
      let uu____1775 = FStar_Options.ugly () in Prims.op_Negation uu____1775 in
    if uu____1774
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1780 -> ""
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
           (lid,univs1,tps,k,uu____1789,uu____1790) ->
           let uu____1795 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1796 = binders_to_string " " tps in
           let uu____1797 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1795
             lid.FStar_Ident.str uu____1796 uu____1797
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1801,uu____1802,uu____1803) ->
           let uu____1806 = FStar_Options.print_universes () in
           if uu____1806
           then
             let uu____1807 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1807 with
              | (univs2,t1) ->
                  let uu____1812 = univ_names_to_string univs2 in
                  let uu____1813 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1812
                    lid.FStar_Ident.str uu____1813)
           else
             (let uu____1815 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1815)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1819 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1819 with
            | (univs2,t1) ->
                let uu____1824 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1825 =
                  let uu____1826 = FStar_Options.print_universes () in
                  if uu____1826
                  then
                    let uu____1827 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1827
                  else "" in
                let uu____1829 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1824
                  lid.FStar_Ident.str uu____1825 uu____1829)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____1831,f) ->
           let uu____1833 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1833
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1835,uu____1836) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1842 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1842
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1844) ->
           let uu____1849 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1849 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1861) -> lift_wp
             | (uu____1865,Some lift) -> lift in
           let uu____1870 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1870 with
            | (us,t) ->
                let uu____1877 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1878 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1879 = univ_names_to_string us in
                let uu____1880 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1877
                  uu____1878 uu____1879 uu____1880)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1888 = FStar_Options.print_universes () in
           if uu____1888
           then
             let uu____1889 =
               let uu____1892 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c)) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1892 in
             (match uu____1889 with
              | (univs2,t) ->
                  let uu____1899 =
                    let uu____1907 =
                      let uu____1908 = FStar_Syntax_Subst.compress t in
                      uu____1908.FStar_Syntax_Syntax.n in
                    match uu____1907 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1935 -> failwith "impossible" in
                  (match uu____1899 with
                   | (tps1,c1) ->
                       let uu____1955 = sli l in
                       let uu____1956 = univ_names_to_string univs2 in
                       let uu____1957 = binders_to_string " " tps1 in
                       let uu____1958 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1955
                         uu____1956 uu____1957 uu____1958))
           else
             (let uu____1960 = sli l in
              let uu____1961 = binders_to_string " " tps in
              let uu____1962 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1960 uu____1961
                uu____1962))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1969 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1969 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1973,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1975;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1977;
                       FStar_Syntax_Syntax.lbdef = uu____1978;_}::[]),uu____1979,uu____1980)
        ->
        let uu____1996 = lbname_to_string lb in
        let uu____1997 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1996 uu____1997
    | uu____1998 ->
        let uu____1999 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1999 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2009 = sli m.FStar_Syntax_Syntax.name in
    let uu____2010 =
      let uu____2011 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2011 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2009 uu____2010
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___207_2016  ->
    match uu___207_2016 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2019 = FStar_Util.string_of_int i in
        let uu____2020 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2019 uu____2020
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2023 = bv_to_string x in
        let uu____2024 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2023 uu____2024
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2031 = bv_to_string x in
        let uu____2032 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2031 uu____2032
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2035 = FStar_Util.string_of_int i in
        let uu____2036 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2035 uu____2036
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2039 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2039
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2043 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2043 (FStar_String.concat "; ")
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
       (let uu____2093 = f x in
        FStar_Util.string_builder_append strb uu____2093);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2100 = f x1 in
             FStar_Util.string_builder_append strb uu____2100)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2129 = f x in
        FStar_Util.string_builder_append strb uu____2129);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2136 = f x1 in
             FStar_Util.string_builder_append strb uu____2136)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)