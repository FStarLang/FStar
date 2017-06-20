open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___210_4  ->
    match uu___210_4 with
    | FStar_Syntax_Syntax.Delta_constant  -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____6 = FStar_Util.string_of_int i in
        Prims.strcat "Delta_defined_at_level " uu____6
    | FStar_Syntax_Syntax.Delta_equational  -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____8 =
          let uu____9 = delta_depth_to_string d in Prims.strcat uu____9 ")" in
        Prims.strcat "Delta_abstract (" uu____8
let sli: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____14 = FStar_Options.print_real_names () in
    if uu____14
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let lid_to_string: FStar_Ident.lid -> Prims.string = fun l  -> sli l
let fv_to_string: FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let bv_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____32 =
      let uu____33 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____33 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____32
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____38 = FStar_Options.print_real_names () in
    if uu____38
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____44 =
      let uu____45 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____45 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____44
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
  | uu____127 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____146 -> failwith "get_lid"
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
let is_inr uu___211_203 =
  match uu___211_203 with
  | FStar_Util.Inl uu____206 -> false
  | FStar_Util.Inr uu____207 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___212_240  ->
          match uu___212_240 with
          | (uu____244,Some (FStar_Syntax_Syntax.Implicit uu____245)) ->
              false
          | uu____247 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list option
  =
  fun e  ->
    let uu____259 =
      let uu____260 = FStar_Syntax_Subst.compress e in
      uu____260.FStar_Syntax_Syntax.n in
    match uu____259 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives.fst args1 in
        let uu____306 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____306
        then
          let uu____317 =
            let uu____322 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____322 in
          (match uu____317 with
           | Some xs ->
               let uu____336 =
                 let uu____340 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____340 :: xs in
               Some uu____336
           | None  -> None)
        else None
    | uu____360 ->
        let uu____361 = is_lex_top e in if uu____361 then Some [] else None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____400 = f hd1 in if uu____400 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident* Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____416 = find (fun p  -> FStar_Ident.lid_equals x (fst p)) xs in
      snd uu____416
let infix_prim_op_to_string e =
  let uu____437 = get_lid e in find_lid uu____437 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____451 = get_lid e in find_lid uu____451 unary_prim_ops
let quant_to_string t =
  let uu____465 = get_lid t in find_lid uu____465 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____474) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____477 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____482) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____492 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____492
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___213_496  ->
    match uu___213_496 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____508 = db_to_string x in Prims.strcat "Tm_bvar: " uu____508
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____510 = nm_to_string x in Prims.strcat "Tm_name: " uu____510
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____512 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____512
    | FStar_Syntax_Syntax.Tm_uinst uu____517 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____522 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____523 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____524 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____534 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____542 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____547 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____557 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____573 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____591 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____599 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____608,m) ->
        let uu____634 = FStar_ST.read m in
        (match uu____634 with
         | None  -> "Tm_delayed"
         | Some uu____645 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____650 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____659 = FStar_Options.hide_uvar_nums () in
    if uu____659
    then "?"
    else
      (let uu____661 =
         let uu____662 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____662 FStar_Util.string_of_int in
       Prims.strcat "?" uu____661)
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____667 = FStar_Options.hide_uvar_nums () in
    if uu____667
    then "?"
    else
      (let uu____669 =
         let uu____670 = FStar_Syntax_Unionfind.univ_uvar_id u in
         FStar_All.pipe_right uu____670 FStar_Util.string_of_int in
       Prims.strcat "?" uu____669)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____682 = FStar_Syntax_Subst.compress_univ u in
      match uu____682 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____688 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____694 =
      let uu____695 = FStar_Options.ugly () in Prims.op_Negation uu____695 in
    if uu____694
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____699 = FStar_Syntax_Subst.compress_univ u in
       match uu____699 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____705 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____705
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____707 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____707 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____716 = univ_to_string u2 in
                let uu____717 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____716 uu____717)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____720 =
             let uu____721 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____721 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____720
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____730 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____730 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____739 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____739 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___214_746  ->
    match uu___214_746 with
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
        let uu____748 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____748
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____751 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____751 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____758 =
          let uu____759 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____759 in
        let uu____761 =
          let uu____762 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____762 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____758 uu____761
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____773 =
          let uu____774 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____774 in
        let uu____776 =
          let uu____777 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____777 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____773 uu____776
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____783 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____783
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
    | uu____791 ->
        let uu____793 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____793 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____804 ->
        let uu____806 = quals_to_string quals in Prims.strcat uu____806 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____854 =
      let uu____855 = FStar_Options.ugly () in Prims.op_Negation uu____855 in
    if uu____854
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____861 = FStar_Options.print_implicits () in
         if uu____861 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____863 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____878,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____905 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____921 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____929  ->
                                 match uu____929 with
                                 | (t1,uu____933) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____921
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____905 (FStar_String.concat "\\/") in
           let uu____936 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____936
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____948 = tag_of_term t in
           let uu____949 = sli m in
           let uu____950 = term_to_string t' in
           let uu____951 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____948 uu____949
             uu____950 uu____951
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____964 = tag_of_term t in
           let uu____965 = term_to_string t' in
           let uu____966 = sli m0 in
           let uu____967 = sli m1 in
           let uu____968 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____964
             uu____965 uu____966 uu____967 uu____968
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____970,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____984 = FStar_Range.string_of_range r in
           let uu____985 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____984
             uu____985
       | FStar_Syntax_Syntax.Tm_meta (t,uu____987) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____996) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1011 = FStar_Options.print_universes () in
           if uu____1011
           then
             let uu____1012 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1012
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1026 = binders_to_string " -> " bs in
           let uu____1027 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1026 uu____1027
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some rc when FStar_Options.print_implicits () ->
                let uu____1044 = binders_to_string " " bs in
                let uu____1045 = term_to_string t2 in
                let uu____1046 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1050 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1050) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1044 uu____1045
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1046
            | uu____1053 ->
                let uu____1055 = binders_to_string " " bs in
                let uu____1056 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1055 uu____1056)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1063 = bv_to_string xt in
           let uu____1064 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1067 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1063 uu____1064 uu____1067
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1086 = term_to_string t in
           let uu____1087 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1086 uu____1087
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1100 = lbs_to_string [] lbs in
           let uu____1101 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1100 uu____1101
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1149 =
                   let uu____1150 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1150
                     (FStar_Util.dflt "default") in
                 let uu____1153 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1149 uu____1153
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1169 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1169 in
           let uu____1170 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1170 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1199 = term_to_string head1 in
           let uu____1200 =
             let uu____1201 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1219  ->
                       match uu____1219 with
                       | (p,wopt,e) ->
                           let uu____1229 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1230 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1232 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1232 in
                           let uu____1233 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1229
                             uu____1230 uu____1233)) in
             FStar_Util.concat_l "\n\t|" uu____1201 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1199 uu____1200
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1240 = FStar_Options.print_universes () in
           if uu____1240
           then
             let uu____1241 = term_to_string t in
             let uu____1242 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1241 uu____1242
           else term_to_string t
       | uu____1244 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1246 =
      let uu____1247 = FStar_Options.ugly () in Prims.op_Negation uu____1247 in
    if uu____1246
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1263 = fv_to_string l in
           let uu____1264 =
             let uu____1265 =
               FStar_List.map
                 (fun uu____1269  ->
                    match uu____1269 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1265 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1263 uu____1264
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1278) ->
           let uu____1283 = FStar_Options.print_bound_var_types () in
           if uu____1283
           then
             let uu____1284 = bv_to_string x1 in
             let uu____1285 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1284 uu____1285
           else
             (let uu____1287 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1287)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1289 = FStar_Options.print_bound_var_types () in
           if uu____1289
           then
             let uu____1290 = bv_to_string x1 in
             let uu____1291 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1290 uu____1291
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1295 = FStar_Options.print_real_names () in
           if uu____1295
           then
             let uu____1296 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1296
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1308 = FStar_Options.print_universes () in
        if uu____1308
        then
          let uu____1312 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1318 =
                      let uu____1321 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1321 in
                    match uu____1318 with
                    | (us,td) ->
                        let uu____1324 =
                          let uu____1331 =
                            let uu____1332 = FStar_Syntax_Subst.compress td in
                            uu____1332.FStar_Syntax_Syntax.n in
                          match uu____1331 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1341,(t,uu____1343)::(d,uu____1345)::[])
                              -> (t, d)
                          | uu____1379 -> failwith "Impossibe" in
                        (match uu____1324 with
                         | (t,d) ->
                             let uu___221_1396 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___221_1396.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___221_1396.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1312)
        else lbs in
      let uu____1400 = quals_to_string' quals in
      let uu____1401 =
        let uu____1402 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1408 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1409 =
                    let uu____1410 = FStar_Options.print_universes () in
                    if uu____1410
                    then
                      let uu____1411 =
                        let uu____1412 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1412 ">" in
                      Prims.strcat "<" uu____1411
                    else "" in
                  let uu____1414 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1415 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1408 uu____1409
                    uu____1414 uu____1415)) in
        FStar_Util.concat_l "\n and " uu____1402 in
      FStar_Util.format3 "%slet %s %s" uu____1400
        (if fst lbs1 then "rec" else "") uu____1401
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1421 = FStar_Options.print_effect_args () in
    if uu____1421
    then
      let uu____1422 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1422
    else
      (let uu____1424 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1425 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1424 uu____1425)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___215_1427  ->
      match uu___215_1427 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1429 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1433 =
        let uu____1434 = FStar_Options.ugly () in
        Prims.op_Negation uu____1434 in
      if uu____1433
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1438 = b in
         match uu____1438 with
         | (a,imp) ->
             let uu____1441 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1441
             then
               let uu____1442 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1442
             else
               (let uu____1444 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1445 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1445) in
                if uu____1444
                then
                  let uu____1446 = nm_to_string a in
                  imp_to_string uu____1446 imp
                else
                  (let uu____1448 =
                     let uu____1449 = nm_to_string a in
                     let uu____1450 =
                       let uu____1451 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1451 in
                     Prims.strcat uu____1449 uu____1450 in
                   imp_to_string uu____1448 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1457 = FStar_Options.print_implicits () in
        if uu____1457 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1459 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1459 (FStar_String.concat sep)
      else
        (let uu____1464 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1464 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___216_1468  ->
    match uu___216_1468 with
    | (a,imp) ->
        let uu____1476 = term_to_string a in imp_to_string uu____1476 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1479 = FStar_Options.print_implicits () in
      if uu____1479 then args else filter_imp args in
    let uu____1483 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1483 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1491 =
      let uu____1492 = FStar_Options.ugly () in Prims.op_Negation uu____1492 in
    if uu____1491
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1497) ->
           let uu____1504 =
             let uu____1505 = FStar_Syntax_Subst.compress t in
             uu____1505.FStar_Syntax_Syntax.n in
           (match uu____1504 with
            | FStar_Syntax_Syntax.Tm_type uu____1508 when
                let uu____1509 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1509 -> term_to_string t
            | uu____1510 ->
                let uu____1511 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____1511)
       | FStar_Syntax_Syntax.GTotal (t,uu____1513) ->
           let uu____1520 =
             let uu____1521 = FStar_Syntax_Subst.compress t in
             uu____1521.FStar_Syntax_Syntax.n in
           (match uu____1520 with
            | FStar_Syntax_Syntax.Tm_type uu____1524 when
                let uu____1525 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1525 -> term_to_string t
            | uu____1526 ->
                let uu____1527 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____1527)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1530 = FStar_Options.print_effect_args () in
             if uu____1530
             then
               let uu____1531 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1532 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1533 =
                 let uu____1534 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1534 (FStar_String.concat ", ") in
               let uu____1546 =
                 let uu____1547 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1547 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1531
                 uu____1532 uu____1533 uu____1546
             else
               (let uu____1553 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___217_1555  ->
                           match uu___217_1555 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1556 -> false)))
                    &&
                    (let uu____1557 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1557) in
                if uu____1553
                then
                  let uu____1558 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1558
                else
                  (let uu____1560 =
                     ((let uu____1561 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1561) &&
                        (let uu____1562 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1562))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1560
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1564 =
                        (let uu____1565 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1565) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___218_1567  ->
                                   match uu___218_1567 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1568 -> false))) in
                      if uu____1564
                      then
                        let uu____1569 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1569
                      else
                        (let uu____1571 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1572 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1571 uu____1572)))) in
           let dec =
             let uu____1574 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___219_1578  ->
                       match uu___219_1578 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1583 =
                             let uu____1584 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1584 in
                           [uu____1583]
                       | uu____1585 -> [])) in
             FStar_All.pipe_right uu____1574 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1588 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1598 = FStar_Options.print_universes () in
    if uu____1598 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1604 =
      let uu____1605 = FStar_Options.ugly () in Prims.op_Negation uu____1605 in
    if uu____1604
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1609 = s in
       match uu____1609 with
       | (us,t) ->
           let uu____1614 =
             let uu____1615 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1615 in
           let uu____1616 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1614 uu____1616)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____1621 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____1622 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____1623 =
      let uu____1624 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____1624 in
    let uu____1625 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____1626 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____1621 uu____1622 uu____1623
      uu____1625 uu____1626
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
          let uu____1645 =
            let uu____1646 = FStar_Options.ugly () in
            Prims.op_Negation uu____1646 in
          if uu____1645
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1656 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____1656 (FStar_String.concat ",\n\t") in
             let uu____1661 =
               let uu____1663 =
                 let uu____1665 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1666 =
                   let uu____1668 =
                     let uu____1669 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1669 in
                   let uu____1670 =
                     let uu____1672 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1673 =
                       let uu____1675 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1676 =
                         let uu____1678 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1679 =
                           let uu____1681 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1682 =
                             let uu____1684 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1685 =
                               let uu____1687 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1688 =
                                 let uu____1690 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1691 =
                                   let uu____1693 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1694 =
                                     let uu____1696 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1697 =
                                       let uu____1699 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1700 =
                                         let uu____1702 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1703 =
                                           let uu____1705 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1706 =
                                             let uu____1708 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1709 =
                                               let uu____1711 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1712 =
                                                 let uu____1714 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1715 =
                                                   let uu____1717 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1717] in
                                                 uu____1714 :: uu____1715 in
                                               uu____1711 :: uu____1712 in
                                             uu____1708 :: uu____1709 in
                                           uu____1705 :: uu____1706 in
                                         uu____1702 :: uu____1703 in
                                       uu____1699 :: uu____1700 in
                                     uu____1696 :: uu____1697 in
                                   uu____1693 :: uu____1694 in
                                 uu____1690 :: uu____1691 in
                               uu____1687 :: uu____1688 in
                             uu____1684 :: uu____1685 in
                           uu____1681 :: uu____1682 in
                         uu____1678 :: uu____1679 in
                       uu____1675 :: uu____1676 in
                     uu____1672 :: uu____1673 in
                   uu____1668 :: uu____1670 in
                 uu____1665 :: uu____1666 in
               (if for_free then "_for_free " else "") :: uu____1663 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1661)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1731 =
      let uu____1732 = FStar_Options.ugly () in Prims.op_Negation uu____1732 in
    if uu____1731
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1737 -> ""
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
           (lid,univs1,tps,k,uu____1746,uu____1747) ->
           let uu____1752 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1753 = binders_to_string " " tps in
           let uu____1754 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1752
             lid.FStar_Ident.str uu____1753 uu____1754
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1758,uu____1759,uu____1760) ->
           let uu____1763 = FStar_Options.print_universes () in
           if uu____1763
           then
             let uu____1764 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1764 with
              | (univs2,t1) ->
                  let uu____1769 = univ_names_to_string univs2 in
                  let uu____1770 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1769
                    lid.FStar_Ident.str uu____1770)
           else
             (let uu____1772 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1772)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1776 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1776 with
            | (univs2,t1) ->
                let uu____1781 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1782 =
                  let uu____1783 = FStar_Options.print_universes () in
                  if uu____1783
                  then
                    let uu____1784 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1784
                  else "" in
                let uu____1786 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1781
                  lid.FStar_Ident.str uu____1782 uu____1786)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____1789 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1789
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1791,uu____1792) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1798 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1798
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1800) ->
           let uu____1805 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1805 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1817) -> lift_wp
             | (uu____1821,Some lift) -> lift in
           let uu____1826 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1826 with
            | (us,t) ->
                let uu____1833 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1834 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1835 = univ_names_to_string us in
                let uu____1836 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1833
                  uu____1834 uu____1835 uu____1836)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1844 = FStar_Options.print_universes () in
           if uu____1844
           then
             let uu____1845 =
               let uu____1848 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1848 in
             (match uu____1845 with
              | (univs2,t) ->
                  let uu____1859 =
                    let uu____1867 =
                      let uu____1868 = FStar_Syntax_Subst.compress t in
                      uu____1868.FStar_Syntax_Syntax.n in
                    match uu____1867 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1895 -> failwith "impossible" in
                  (match uu____1859 with
                   | (tps1,c1) ->
                       let uu____1915 = sli l in
                       let uu____1916 = univ_names_to_string univs2 in
                       let uu____1917 = binders_to_string " " tps1 in
                       let uu____1918 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1915
                         uu____1916 uu____1917 uu____1918))
           else
             (let uu____1920 = sli l in
              let uu____1921 = binders_to_string " " tps in
              let uu____1922 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1920 uu____1921
                uu____1922))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1931 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1931 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1936,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1938;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1940;
                       FStar_Syntax_Syntax.lbdef = uu____1941;_}::[]),uu____1942,uu____1943)
        ->
        let uu____1959 = lbname_to_string lb in
        let uu____1960 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1959 uu____1960
    | uu____1961 ->
        let uu____1962 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1962 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1972 = sli m.FStar_Syntax_Syntax.name in
    let uu____1973 =
      let uu____1974 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1974 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1972 uu____1973
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___220_1980  ->
    match uu___220_1980 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1983 = FStar_Util.string_of_int i in
        let uu____1984 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1983 uu____1984
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1987 = bv_to_string x in
        let uu____1988 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1987 uu____1988
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1995 = bv_to_string x in
        let uu____1996 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1995 uu____1996
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1999 = FStar_Util.string_of_int i in
        let uu____2000 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1999 uu____2000
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2003 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2003
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2008 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2008 (FStar_String.concat "; ")
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
       (let uu____2062 = f x in
        FStar_Util.string_builder_append strb uu____2062);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2066 = f x1 in
             FStar_Util.string_builder_append strb uu____2066)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2098 = f x in
        FStar_Util.string_builder_append strb uu____2098);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2102 = f x1 in
             FStar_Util.string_builder_append strb uu____2102)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)