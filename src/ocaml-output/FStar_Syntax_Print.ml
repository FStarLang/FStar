open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___209_3  ->
    match uu___209_3 with
    | FStar_Syntax_Syntax.Delta_constant  -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____5 = FStar_Util.string_of_int i in
        Prims.strcat "Delta_defined_at_level " uu____5
    | FStar_Syntax_Syntax.Delta_equational  -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____7 =
          let uu____8 = delta_depth_to_string d in Prims.strcat uu____8 ")" in
        Prims.strcat "Delta_abstract (" uu____7
let sli: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____12 = FStar_Options.print_real_names () in
    if uu____12
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let lid_to_string: FStar_Ident.lid -> Prims.string = fun l  -> sli l
let fv_to_string: FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let bv_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____27 =
      let uu____28 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____28 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____27
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____32 = FStar_Options.print_real_names () in
    if uu____32
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____37 =
      let uu____38 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____38 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____37
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
  | uu____117 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____134 -> failwith "get_lid"
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
let is_inr uu___210_181 =
  match uu___210_181 with
  | FStar_Util.Inl uu____184 -> false
  | FStar_Util.Inr uu____185 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___211_216  ->
          match uu___211_216 with
          | (uu____220,Some (FStar_Syntax_Syntax.Implicit uu____221)) ->
              false
          | uu____223 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list option
  =
  fun e  ->
    let uu____234 =
      let uu____235 = FStar_Syntax_Subst.compress e in
      uu____235.FStar_Syntax_Syntax.n in
    match uu____234 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives.fst args1 in
        let uu____281 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____281
        then
          let uu____292 =
            let uu____297 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____297 in
          (match uu____292 with
           | Some xs ->
               let uu____311 =
                 let uu____315 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____315 :: xs in
               Some uu____311
           | None  -> None)
        else None
    | uu____335 ->
        let uu____336 = is_lex_top e in if uu____336 then Some [] else None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____372 = f hd1 in if uu____372 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident* Prims.string) Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____386 = find (fun p  -> FStar_Ident.lid_equals x (fst p)) xs in
      snd uu____386
let infix_prim_op_to_string e =
  let uu____405 = get_lid e in find_lid uu____405 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____417 = get_lid e in find_lid uu____417 unary_prim_ops
let quant_to_string t =
  let uu____429 = get_lid t in find_lid uu____429 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____437) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____440 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____445) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____455 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____455
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___212_458  ->
    match uu___212_458 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____469 = db_to_string x in Prims.strcat "Tm_bvar: " uu____469
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____471 = nm_to_string x in Prims.strcat "Tm_name: " uu____471
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____473 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____473
    | FStar_Syntax_Syntax.Tm_uinst uu____478 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____483 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____484 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____485 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____500 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____508 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____513 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____523 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____539 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____557 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____565 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____574,m) ->
        let uu____612 = FStar_ST.read m in
        (match uu____612 with
         | None  -> "Tm_delayed"
         | Some uu____623 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____628 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____636 = FStar_Options.hide_uvar_nums () in
    if uu____636
    then "?"
    else
      (let uu____638 =
         let uu____639 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____639 FStar_Util.string_of_int in
       Prims.strcat "?" uu____638)
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____643 = FStar_Options.hide_uvar_nums () in
    if uu____643
    then "?"
    else
      (let uu____645 =
         let uu____646 = FStar_Syntax_Unionfind.univ_uvar_id u in
         FStar_All.pipe_right uu____646 FStar_Util.string_of_int in
       Prims.strcat "?" uu____645)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe option)
  =
  fun n1  ->
    fun u  ->
      let uu____656 = FStar_Syntax_Subst.compress_univ u in
      match uu____656 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____662 -> (n1, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____667 =
      let uu____668 = FStar_Options.ugly () in Prims.op_Negation uu____668 in
    if uu____667
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____672 = FStar_Syntax_Subst.compress_univ u in
       match uu____672 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____678 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____678
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____680 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____680 with
            | (n1,None ) -> FStar_Util.string_of_int n1
            | (n1,Some u2) ->
                let uu____689 = univ_to_string u2 in
                let uu____690 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____689 uu____690)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____693 =
             let uu____694 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____694 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____693
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____702 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____702 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____710 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____710 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___213_716  ->
    match uu___213_716 with
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
        let uu____718 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____718
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____721 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____721 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____728 =
          let uu____729 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____729 in
        let uu____731 =
          let uu____732 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____732 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____728 uu____731
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____743 =
          let uu____744 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____744 in
        let uu____746 =
          let uu____747 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____747 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____743 uu____746
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____753 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____753
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
    | uu____760 ->
        let uu____762 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____762 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____772 ->
        let uu____774 = quals_to_string quals in Prims.strcat uu____774 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____822 =
      let uu____823 = FStar_Options.ugly () in Prims.op_Negation uu____823 in
    if uu____822
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____829 = FStar_Options.print_implicits () in
         if uu____829 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____831 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____852,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____879 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____895 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____903  ->
                                 match uu____903 with
                                 | (t1,uu____907) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____895
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____879 (FStar_String.concat "\\/") in
           let uu____910 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____910
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____922 = tag_of_term t in
           let uu____923 = sli m in
           let uu____924 = term_to_string t' in
           let uu____925 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____922 uu____923
             uu____924 uu____925
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____938 = tag_of_term t in
           let uu____939 = term_to_string t' in
           let uu____940 = sli m0 in
           let uu____941 = sli m1 in
           let uu____942 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____938
             uu____939 uu____940 uu____941 uu____942
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____951 = FStar_Range.string_of_range r in
           let uu____952 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____951
             uu____952
       | FStar_Syntax_Syntax.Tm_meta (t,uu____954) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____963) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____978 = FStar_Options.print_universes () in
           if uu____978
           then
             let uu____979 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____979
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____993 = binders_to_string " -> " bs in
           let uu____994 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____993 uu____994
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | Some (FStar_Util.Inl l) when FStar_Options.print_implicits ()
                ->
                let uu____1029 = binders_to_string " " bs in
                let uu____1030 = term_to_string t2 in
                let uu____1031 =
                  let uu____1032 = l.FStar_Syntax_Syntax.comp () in
                  FStar_All.pipe_left comp_to_string uu____1032 in
                FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1029
                  uu____1030 uu____1031
            | Some (FStar_Util.Inr (l,flags)) when
                FStar_Options.print_implicits () ->
                let uu____1045 = binders_to_string " " bs in
                let uu____1046 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____1045 uu____1046 l.FStar_Ident.str
            | uu____1047 ->
                let uu____1054 = binders_to_string " " bs in
                let uu____1055 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1054 uu____1055)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1062 = bv_to_string xt in
           let uu____1063 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1066 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1062 uu____1063 uu____1066
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1085 = term_to_string t in
           let uu____1086 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1085 uu____1086
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1099 = lbs_to_string [] lbs in
           let uu____1100 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1099 uu____1100
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1148 =
                   let uu____1149 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1149
                     (FStar_Util.dflt "default") in
                 let uu____1152 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1148 uu____1152
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | None  -> ""
             | Some t ->
                 let uu____1168 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1168 in
           let uu____1169 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1169 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1198 = term_to_string head1 in
           let uu____1199 =
             let uu____1200 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1218  ->
                       match uu____1218 with
                       | (p,wopt,e) ->
                           let uu____1228 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1229 =
                             match wopt with
                             | None  -> ""
                             | Some w ->
                                 let uu____1231 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1231 in
                           let uu____1232 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1228
                             uu____1229 uu____1232)) in
             FStar_Util.concat_l "\n\t|" uu____1200 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1198 uu____1199
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1239 = FStar_Options.print_universes () in
           if uu____1239
           then
             let uu____1240 = term_to_string t in
             let uu____1241 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1240 uu____1241
           else term_to_string t
       | uu____1243 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1245 =
      let uu____1246 = FStar_Options.ugly () in Prims.op_Negation uu____1246 in
    if uu____1245
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1262 = fv_to_string l in
           let uu____1263 =
             let uu____1264 =
               FStar_List.map
                 (fun uu____1268  ->
                    match uu____1268 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1264 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1262 uu____1263
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1277) ->
           let uu____1282 = FStar_Options.print_bound_var_types () in
           if uu____1282
           then
             let uu____1283 = bv_to_string x1 in
             let uu____1284 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1283 uu____1284
           else
             (let uu____1286 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1286)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1288 = FStar_Options.print_bound_var_types () in
           if uu____1288
           then
             let uu____1289 = bv_to_string x1 in
             let uu____1290 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1289 uu____1290
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1294 = FStar_Options.print_real_names () in
           if uu____1294
           then
             let uu____1295 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1295
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1307 = FStar_Options.print_universes () in
        if uu____1307
        then
          let uu____1311 =
            FStar_All.pipe_right (snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1317 =
                      let uu____1320 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1320 in
                    match uu____1317 with
                    | (us,td) ->
                        let uu____1323 =
                          let uu____1330 =
                            let uu____1331 = FStar_Syntax_Subst.compress td in
                            uu____1331.FStar_Syntax_Syntax.n in
                          match uu____1330 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1340,(t,uu____1342)::(d,uu____1344)::[])
                              -> (t, d)
                          | uu____1378 -> failwith "Impossibe" in
                        (match uu____1323 with
                         | (t,d) ->
                             let uu___220_1395 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___220_1395.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___220_1395.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((fst lbs), uu____1311)
        else lbs in
      let uu____1399 = quals_to_string' quals in
      let uu____1400 =
        let uu____1401 =
          FStar_All.pipe_right (snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1407 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1408 =
                    let uu____1409 = FStar_Options.print_universes () in
                    if uu____1409
                    then
                      let uu____1410 =
                        let uu____1411 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1411 ">" in
                      Prims.strcat "<" uu____1410
                    else "" in
                  let uu____1413 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1414 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1407 uu____1408
                    uu____1413 uu____1414)) in
        FStar_Util.concat_l "\n and " uu____1401 in
      FStar_Util.format3 "%slet %s %s" uu____1399
        (if fst lbs1 then "rec" else "") uu____1400
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1420 = FStar_Options.print_effect_args () in
    if uu____1420
    then
      let uu____1421 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1421
    else
      (let uu____1423 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1424 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1423 uu____1424)
and imp_to_string:
  Prims.string -> FStar_Syntax_Syntax.arg_qualifier option -> Prims.string =
  fun s  ->
    fun uu___214_1426  ->
      match uu___214_1426 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1428 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1432 =
        let uu____1433 = FStar_Options.ugly () in
        Prims.op_Negation uu____1433 in
      if uu____1432
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1437 = b in
         match uu____1437 with
         | (a,imp) ->
             let uu____1440 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1440
             then
               let uu____1441 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1441
             else
               (let uu____1443 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1444 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1444) in
                if uu____1443
                then
                  let uu____1445 = nm_to_string a in
                  imp_to_string uu____1445 imp
                else
                  (let uu____1447 =
                     let uu____1448 = nm_to_string a in
                     let uu____1449 =
                       let uu____1450 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1450 in
                     Prims.strcat uu____1448 uu____1449 in
                   imp_to_string uu____1447 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1456 = FStar_Options.print_implicits () in
        if uu____1456 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1458 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1458 (FStar_String.concat sep)
      else
        (let uu____1463 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1463 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier option) ->
    Prims.string
  =
  fun uu___215_1467  ->
    match uu___215_1467 with
    | (a,imp) ->
        let uu____1475 = term_to_string a in imp_to_string uu____1475 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1478 = FStar_Options.print_implicits () in
      if uu____1478 then args else filter_imp args in
    let uu____1482 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1482 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1490 =
      let uu____1491 = FStar_Options.ugly () in Prims.op_Negation uu____1491 in
    if uu____1490
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____1496) ->
           let uu____1503 =
             let uu____1504 = FStar_Syntax_Subst.compress t in
             uu____1504.FStar_Syntax_Syntax.n in
           (match uu____1503 with
            | FStar_Syntax_Syntax.Tm_type uu____1507 when
                let uu____1508 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1508 -> term_to_string t
            | uu____1509 ->
                let uu____1510 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____1510)
       | FStar_Syntax_Syntax.GTotal (t,uu____1512) ->
           let uu____1519 =
             let uu____1520 = FStar_Syntax_Subst.compress t in
             uu____1520.FStar_Syntax_Syntax.n in
           (match uu____1519 with
            | FStar_Syntax_Syntax.Tm_type uu____1523 when
                let uu____1524 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____1524 -> term_to_string t
            | uu____1525 ->
                let uu____1526 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____1526)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1529 = FStar_Options.print_effect_args () in
             if uu____1529
             then
               let uu____1530 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1531 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1532 =
                 let uu____1533 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1533 (FStar_String.concat ", ") in
               let uu____1545 =
                 let uu____1546 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1546 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1530
                 uu____1531 uu____1532 uu____1545
             else
               (let uu____1552 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___216_1554  ->
                           match uu___216_1554 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1555 -> false)))
                    &&
                    (let uu____1556 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1556) in
                if uu____1552
                then
                  let uu____1557 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1557
                else
                  (let uu____1559 =
                     ((let uu____1560 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1560) &&
                        (let uu____1561 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1561))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Syntax_Const.effect_ML_lid) in
                   if uu____1559
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1563 =
                        (let uu____1564 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1564) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___217_1566  ->
                                   match uu___217_1566 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1567 -> false))) in
                      if uu____1563
                      then
                        let uu____1568 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1568
                      else
                        (let uu____1570 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1571 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1570 uu____1571)))) in
           let dec =
             let uu____1573 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___218_1577  ->
                       match uu___218_1577 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1582 =
                             let uu____1583 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1583 in
                           [uu____1582]
                       | uu____1584 -> [])) in
             FStar_All.pipe_right uu____1573 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1587 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1596 = FStar_Options.print_universes () in
    if uu____1596 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1601 =
      let uu____1602 = FStar_Options.ugly () in Prims.op_Negation uu____1602 in
    if uu____1601
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1606 = s in
       match uu____1606 with
       | (us,t) ->
           let uu____1611 =
             let uu____1612 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1612 in
           let uu____1613 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1611 uu____1613)
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
          let uu____1628 =
            let uu____1629 = FStar_Options.ugly () in
            Prims.op_Negation uu____1629 in
          if uu____1628
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1639 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____1644 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____1645 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____1646 =
                           let uu____1647 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____1647 in
                         let uu____1648 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____1649 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____1644
                           uu____1645 uu____1646 uu____1648 uu____1649)) in
               FStar_All.pipe_right uu____1639 (FStar_String.concat ",\n\t") in
             let uu____1651 =
               let uu____1653 =
                 let uu____1655 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1656 =
                   let uu____1658 =
                     let uu____1659 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1659 in
                   let uu____1660 =
                     let uu____1662 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1663 =
                       let uu____1665 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1666 =
                         let uu____1668 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1669 =
                           let uu____1671 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1672 =
                             let uu____1674 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1675 =
                               let uu____1677 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1678 =
                                 let uu____1680 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1681 =
                                   let uu____1683 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1684 =
                                     let uu____1686 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1687 =
                                       let uu____1689 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1690 =
                                         let uu____1692 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1693 =
                                           let uu____1695 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1696 =
                                             let uu____1698 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1699 =
                                               let uu____1701 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1702 =
                                                 let uu____1704 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1705 =
                                                   let uu____1707 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1707] in
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
                     uu____1662 :: uu____1663 in
                   uu____1658 :: uu____1660 in
                 uu____1655 :: uu____1656 in
               (if for_free then "_for_free " else "") :: uu____1653 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1651)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1718 =
      let uu____1719 = FStar_Options.ugly () in Prims.op_Negation uu____1719 in
    if uu____1718
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1724 -> ""
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
           (lid,univs1,tps,k,uu____1733,uu____1734) ->
           let uu____1739 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1740 = binders_to_string " " tps in
           let uu____1741 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1739
             lid.FStar_Ident.str uu____1740 uu____1741
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1745,uu____1746,uu____1747) ->
           let uu____1750 = FStar_Options.print_universes () in
           if uu____1750
           then
             let uu____1751 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1751 with
              | (univs2,t1) ->
                  let uu____1756 = univ_names_to_string univs2 in
                  let uu____1757 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1756
                    lid.FStar_Ident.str uu____1757)
           else
             (let uu____1759 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1759)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1763 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1763 with
            | (univs2,t1) ->
                let uu____1768 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1769 =
                  let uu____1770 = FStar_Options.print_universes () in
                  if uu____1770
                  then
                    let uu____1771 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1771
                  else "" in
                let uu____1773 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1768
                  lid.FStar_Ident.str uu____1769 uu____1773)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____1776 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1776
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1778,uu____1779) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1785 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1785
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1787) ->
           let uu____1792 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1792 (FStar_String.concat "\n")
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
             | (Some lift_wp,uu____1804) -> lift_wp
             | (uu____1808,Some lift) -> lift in
           let uu____1813 =
             FStar_Syntax_Subst.open_univ_vars (fst lift_wp) (snd lift_wp) in
           (match uu____1813 with
            | (us,t) ->
                let uu____1820 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1821 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1822 = univ_names_to_string us in
                let uu____1823 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1820
                  uu____1821 uu____1822 uu____1823)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1831 = FStar_Options.print_universes () in
           if uu____1831
           then
             let uu____1832 =
               let uu____1835 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c))) None
                   FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1835 in
             (match uu____1832 with
              | (univs2,t) ->
                  let uu____1846 =
                    let uu____1854 =
                      let uu____1855 = FStar_Syntax_Subst.compress t in
                      uu____1855.FStar_Syntax_Syntax.n in
                    match uu____1854 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1882 -> failwith "impossible" in
                  (match uu____1846 with
                   | (tps1,c1) ->
                       let uu____1902 = sli l in
                       let uu____1903 = univ_names_to_string univs2 in
                       let uu____1904 = binders_to_string " " tps1 in
                       let uu____1905 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1902
                         uu____1903 uu____1904 uu____1905))
           else
             (let uu____1907 = sli l in
              let uu____1908 = binders_to_string " " tps in
              let uu____1909 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1907 uu____1908
                uu____1909))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1916 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1916 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1920,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1922;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1924;
                       FStar_Syntax_Syntax.lbdef = uu____1925;_}::[]),uu____1926,uu____1927)
        ->
        let uu____1943 = lbname_to_string lb in
        let uu____1944 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1943 uu____1944
    | uu____1945 ->
        let uu____1946 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1946 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1955 = sli m.FStar_Syntax_Syntax.name in
    let uu____1956 =
      let uu____1957 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1957 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1955 uu____1956
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___219_1962  ->
    match uu___219_1962 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1965 = FStar_Util.string_of_int i in
        let uu____1966 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1965 uu____1966
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1969 = bv_to_string x in
        let uu____1970 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1969 uu____1970
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1977 = bv_to_string x in
        let uu____1978 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1977 uu____1978
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1981 = FStar_Util.string_of_int i in
        let uu____1982 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1981 uu____1982
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1985 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1985
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1989 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1989 (FStar_String.concat "; ")
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
       (let uu____2039 = f x in
        FStar_Util.string_builder_append strb uu____2039);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2043 = f x1 in
             FStar_Util.string_builder_append strb uu____2043)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2072 = f x in
        FStar_Util.string_builder_append strb uu____2072);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2076 = f x1 in
             FStar_Util.string_builder_append strb uu____2076)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)