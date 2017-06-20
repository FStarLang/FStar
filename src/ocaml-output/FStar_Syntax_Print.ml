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
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____977 = FStar_Range.string_of_range r in
           let uu____978 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____977
             uu____978
       | FStar_Syntax_Syntax.Tm_meta (t,uu____980) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____989) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1004 = FStar_Options.print_universes () in
           if uu____1004
           then
             let uu____1005 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1005
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1019 = binders_to_string " -> " bs in
           let uu____1020 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1019 uu____1020
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some rc when FStar_Options.print_implicits () ->
                let uu____1037 = binders_to_string " " bs in
                let uu____1038 = term_to_string t2 in
                let uu____1039 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1043 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1043) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1037 uu____1038
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1039
            | uu____1046 ->
                let uu____1048 = binders_to_string " " bs in
                let uu____1049 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1048 uu____1049)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1056 = bv_to_string xt in
           let uu____1057 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1060 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1056 uu____1057 uu____1060
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1079 = term_to_string t in
           let uu____1080 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1079 uu____1080
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1093 = lbs_to_string [] lbs in
           let uu____1094 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1093 uu____1094
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1142 =
                   let uu____1143 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1143
                     (FStar_Util.dflt "default") in
                 let uu____1146 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1142 uu____1146
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1162 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1162 in
           let uu____1163 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1163 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1192 = term_to_string head1 in
           let uu____1193 =
             let uu____1194 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1212  ->
                       match uu____1212 with
                       | (p,wopt,e) ->
                           let uu____1222 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1223 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1225 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1225 in
                           let uu____1226 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1222
                             uu____1223 uu____1226)) in
             FStar_Util.concat_l "\n\t|" uu____1194 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1192 uu____1193
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1233 = FStar_Options.print_universes () in
           if uu____1233
           then
             let uu____1234 = term_to_string t in
             let uu____1235 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1234 uu____1235
           else term_to_string t
       | uu____1237 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1239 =
      let uu____1240 = FStar_Options.ugly () in Prims.op_Negation uu____1240 in
    if uu____1239
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1256 = fv_to_string l in
           let uu____1257 =
             let uu____1258 =
               FStar_List.map
                 (fun uu____1262  ->
                    match uu____1262 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1258 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1256 uu____1257
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1271) ->
           let uu____1276 = FStar_Options.print_bound_var_types () in
           if uu____1276
           then
             let uu____1277 = bv_to_string x1 in
             let uu____1278 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1277 uu____1278
           else
             (let uu____1280 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1280)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1282 = FStar_Options.print_bound_var_types () in
           if uu____1282
           then
             let uu____1283 = bv_to_string x1 in
             let uu____1284 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1283 uu____1284
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1288 = FStar_Options.print_real_names () in
           if uu____1288
           then
             let uu____1289 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1289
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1301 = FStar_Options.print_universes () in
        if uu____1301
        then
          let uu____1305 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1311 =
                      let uu____1314 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1314 in
                    match uu____1311 with
                    | (us,td) ->
                        let uu____1317 =
                          let uu____1324 =
                            let uu____1325 = FStar_Syntax_Subst.compress td in
                            uu____1325.FStar_Syntax_Syntax.n in
                          match uu____1324 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1334,(t,uu____1336)::(d,uu____1338)::[])
                              -> (t, d)
                          | uu____1372 -> failwith "Impossibe" in
                        (match uu____1317 with
                         | (t,d) ->
                             let uu___221_1389 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___221_1389.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___221_1389.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1305)
        else lbs in
      let uu____1393 = quals_to_string' quals in
      let uu____1394 =
        let uu____1395 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1401 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1402 =
                    let uu____1403 = FStar_Options.print_universes () in
                    if uu____1403
                    then
                      let uu____1404 =
                        let uu____1405 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1405 ">" in
                      Prims.strcat "<" uu____1404
                    else "" in
                  let uu____1407 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1408 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1401 uu____1402
                    uu____1407 uu____1408)) in
        FStar_Util.concat_l "\n and " uu____1395 in
      FStar_Util.format3 "%slet %s %s" uu____1393
        (if fst lbs1 then "rec" else "") uu____1394
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1414 = FStar_Options.print_effect_args () in
    if uu____1414
    then
      let uu____1415 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1415
    else
      (let uu____1417 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1418 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1417 uu____1418)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___215_1420  ->
      match uu___215_1420 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1422 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1426 =
        let uu____1427 = FStar_Options.ugly () in
        Prims.op_Negation uu____1427 in
      if uu____1426
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1431 = b in
         match uu____1431 with
         | (a,imp) ->
             let uu____1434 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1434
             then
               let uu____1435 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1435
             else
               (let uu____1437 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1438 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1438) in
                if uu____1437
                then
                  let uu____1439 = nm_to_string a in
                  imp_to_string uu____1439 imp
                else
                  (let uu____1441 =
                     let uu____1442 = nm_to_string a in
                     let uu____1443 =
                       let uu____1444 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1444 in
                     Prims.strcat uu____1442 uu____1443 in
                   imp_to_string uu____1441 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
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
        (let uu____1457 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1457 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___216_1461  ->
    match uu___216_1461 with
    | (a,imp) ->
        let uu____1469 = term_to_string a in imp_to_string uu____1469 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1472 = FStar_Options.print_implicits () in
      if uu____1472 then args else filter_imp args in
    let uu____1476 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1476 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1484 =
      let uu____1485 = FStar_Options.ugly () in Prims.op_Negation uu____1485 in
    if uu____1484
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1490) ->
           let uu____1497 =
             let uu____1498 = FStar_Syntax_Subst.compress t in
             uu____1498.FStar_Syntax_Syntax.n in
           (match uu____1497 with
            | FStar_Syntax_Syntax.Tm_type uu____1501 when
                let uu____1502 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1502 -> term_to_string t
            | uu____1503 ->
                let uu____1504 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____1504)
       | FStar_Syntax_Syntax.GTotal (t,uu____1506) ->
           let uu____1513 =
             let uu____1514 = FStar_Syntax_Subst.compress t in
             uu____1514.FStar_Syntax_Syntax.n in
           (match uu____1513 with
            | FStar_Syntax_Syntax.Tm_type uu____1517 when
                let uu____1518 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1518 -> term_to_string t
            | uu____1519 ->
                let uu____1520 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____1520)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1523 = FStar_Options.print_effect_args () in
             if uu____1523
             then
               let uu____1524 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1525 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1526 =
                 let uu____1527 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1527 (FStar_String.concat ", ") in
               let uu____1539 =
                 let uu____1540 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1540 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1524
                 uu____1525 uu____1526 uu____1539
             else
               (let uu____1546 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___217_1548  ->
                           match uu___217_1548 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1549 -> false)))
                    &&
                    (let uu____1550 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1550) in
                if uu____1546
                then
                  let uu____1551 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1551
                else
                  (let uu____1553 =
                     ((let uu____1554 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1554) &&
                        (let uu____1555 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1555))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1553
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1557 =
                        (let uu____1558 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1558) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___218_1560  ->
                                   match uu___218_1560 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1561 -> false))) in
                      if uu____1557
                      then
                        let uu____1562 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1562
                      else
                        (let uu____1564 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1565 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1564 uu____1565)))) in
           let dec =
             let uu____1567 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___219_1571  ->
                       match uu___219_1571 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1576 =
                             let uu____1577 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1577 in
                           [uu____1576]
                       | uu____1578 -> [])) in
             FStar_All.pipe_right uu____1567 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1581 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1591 = FStar_Options.print_universes () in
    if uu____1591 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1597 =
      let uu____1598 = FStar_Options.ugly () in Prims.op_Negation uu____1598 in
    if uu____1597
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1602 = s in
       match uu____1602 with
       | (us,t) ->
           let uu____1607 =
             let uu____1608 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1608 in
           let uu____1609 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1607 uu____1609)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____1614 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____1615 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____1616 =
      let uu____1617 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____1617 in
    let uu____1618 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____1619 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____1614 uu____1615 uu____1616
      uu____1618 uu____1619
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
          let uu____1638 =
            let uu____1639 = FStar_Options.ugly () in
            Prims.op_Negation uu____1639 in
          if uu____1638
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1649 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____1649 (FStar_String.concat ",\n\t") in
             let uu____1654 =
               let uu____1656 =
                 let uu____1658 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1659 =
                   let uu____1661 =
                     let uu____1662 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1662 in
                   let uu____1663 =
                     let uu____1665 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1666 =
                       let uu____1668 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1669 =
                         let uu____1671 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1672 =
                           let uu____1674 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1675 =
                             let uu____1677 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1678 =
                               let uu____1680 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1681 =
                                 let uu____1683 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1684 =
                                   let uu____1686 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1687 =
                                     let uu____1689 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1690 =
                                       let uu____1692 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1693 =
                                         let uu____1695 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1696 =
                                           let uu____1698 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1699 =
                                             let uu____1701 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1702 =
                                               let uu____1704 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1705 =
                                                 let uu____1707 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1708 =
                                                   let uu____1710 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1710] in
                                                 uu____1707 :: uu____1708 in
                                               uu____1704 :: uu____1705 in
                                             uu____1701 :: uu____1702 in
                                           uu____1698 :: uu____1699 in
                                         uu____1695 :: uu____1696 in
                                       uu____1692 :: uu____1693 in
                                     uu____1689 :: uu____1690 in
                                   uu____1686 :: uu____1687 in
                                 uu____1683 :: uu____1684 in
                               uu____1680 :: uu____1681 in
                             uu____1677 :: uu____1678 in
                           uu____1674 :: uu____1675 in
                         uu____1671 :: uu____1672 in
                       uu____1668 :: uu____1669 in
                     uu____1665 :: uu____1666 in
                   uu____1661 :: uu____1663 in
                 uu____1658 :: uu____1659 in
               (if for_free then "_for_free " else "") :: uu____1656 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1654)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1724 =
      let uu____1725 = FStar_Options.ugly () in Prims.op_Negation uu____1725 in
    if uu____1724
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1730 -> ""
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
           (lid,univs1,tps,k,uu____1739,uu____1740) ->
           let uu____1745 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1746 = binders_to_string " " tps in
           let uu____1747 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1745
             lid.FStar_Ident.str uu____1746 uu____1747
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1751,uu____1752,uu____1753) ->
           let uu____1756 = FStar_Options.print_universes () in
           if uu____1756
           then
             let uu____1757 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1757 with
              | (univs2,t1) ->
                  let uu____1762 = univ_names_to_string univs2 in
                  let uu____1763 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1762
                    lid.FStar_Ident.str uu____1763)
           else
             (let uu____1765 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1765)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1769 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1769 with
            | (univs2,t1) ->
                let uu____1774 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1775 =
                  let uu____1776 = FStar_Options.print_universes () in
                  if uu____1776
                  then
                    let uu____1777 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1777
                  else "" in
                let uu____1779 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1774
                  lid.FStar_Ident.str uu____1775 uu____1779)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____1782 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1782
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1784,uu____1785) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1791 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1791
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1793) ->
           let uu____1798 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1798 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1810) -> lift_wp
             | (uu____1814,Some lift) -> lift in
           let uu____1819 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1819 with
            | (us,t) ->
                let uu____1826 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1827 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1828 = univ_names_to_string us in
                let uu____1829 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1826
                  uu____1827 uu____1828 uu____1829)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1837 = FStar_Options.print_universes () in
           if uu____1837
           then
             let uu____1838 =
               let uu____1841 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1841 in
             (match uu____1838 with
              | (univs2,t) ->
                  let uu____1852 =
                    let uu____1860 =
                      let uu____1861 = FStar_Syntax_Subst.compress t in
                      uu____1861.FStar_Syntax_Syntax.n in
                    match uu____1860 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1888 -> failwith "impossible" in
                  (match uu____1852 with
                   | (tps1,c1) ->
                       let uu____1908 = sli l in
                       let uu____1909 = univ_names_to_string univs2 in
                       let uu____1910 = binders_to_string " " tps1 in
                       let uu____1911 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1908
                         uu____1909 uu____1910 uu____1911))
           else
             (let uu____1913 = sli l in
              let uu____1914 = binders_to_string " " tps in
              let uu____1915 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1913 uu____1914
                uu____1915))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1924 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1924 msg
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
    let uu____1965 = sli m.FStar_Syntax_Syntax.name in
    let uu____1966 =
      let uu____1967 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1967 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1965 uu____1966
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___220_1973  ->
    match uu___220_1973 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1976 = FStar_Util.string_of_int i in
        let uu____1977 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1976 uu____1977
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1980 = bv_to_string x in
        let uu____1981 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1980 uu____1981
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1988 = bv_to_string x in
        let uu____1989 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1988 uu____1989
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1992 = FStar_Util.string_of_int i in
        let uu____1993 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1992 uu____1993
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1996 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1996
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2001 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2001 (FStar_String.concat "; ")
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
       (let uu____2055 = f x in
        FStar_Util.string_builder_append strb uu____2055);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2059 = f x1 in
             FStar_Util.string_builder_append strb uu____2059)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2091 = f x in
        FStar_Util.string_builder_append strb uu____2091);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2095 = f x1 in
             FStar_Util.string_builder_append strb uu____2095)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)