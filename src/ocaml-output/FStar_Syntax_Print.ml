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
let is_inr uu___207_173 =
  match uu___207_173 with
  | FStar_Util.Inl uu____176 -> false
  | FStar_Util.Inr uu____177 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___208_208  ->
          match uu___208_208 with
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
  fun uu___209_448  ->
    match uu___209_448 with
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
  fun uu___210_701  ->
    match uu___210_701 with
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
let term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let e = FStar_Syntax_Resugar.resugar_term x in
    let d = FStar_Parser_ToDocument.term_to_document e in
    FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
      (Prims.parse_int "100") d
let rec pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
        let uu____824 = fv_to_string l in
        let uu____825 =
          let uu____826 =
            FStar_List.map
              (fun uu____830  ->
                 match uu____830 with
                 | (x1,b) ->
                     let p = pat_to_string x1 in
                     if b then Prims.strcat "#" p else p) pats in
          FStar_All.pipe_right uu____826 (FStar_String.concat " ") in
        FStar_Util.format2 "(%s %s)" uu____824 uu____825
    | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____839) ->
        let uu____844 = FStar_Options.print_bound_var_types () in
        if uu____844
        then
          let uu____845 = bv_to_string x1 in
          let uu____846 = term_to_string x1.FStar_Syntax_Syntax.sort in
          FStar_Util.format2 ".%s:%s" uu____845 uu____846
        else
          (let uu____848 = bv_to_string x1 in
           FStar_Util.format1 ".%s" uu____848)
    | FStar_Syntax_Syntax.Pat_var x1 ->
        let uu____850 = FStar_Options.print_bound_var_types () in
        if uu____850
        then
          let uu____851 = bv_to_string x1 in
          let uu____852 = term_to_string x1.FStar_Syntax_Syntax.sort in
          FStar_Util.format2 "%s:%s" uu____851 uu____852
        else bv_to_string x1
    | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
    | FStar_Syntax_Syntax.Pat_wild x1 ->
        let uu____856 = FStar_Options.print_real_names () in
        if uu____856
        then
          let uu____857 = bv_to_string x1 in
          Prims.strcat "Pat_wild " uu____857
        else "_"
    | FStar_Syntax_Syntax.Pat_disj ps ->
        let uu____863 = FStar_List.map pat_to_string ps in
        FStar_Util.concat_l " | " uu____863
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____875 = FStar_Options.print_universes () in
        if uu____875
        then
          let uu____879 =
            FStar_All.pipe_right (Prims.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____885 =
                      let uu____888 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____888 in
                    match uu____885 with
                    | (us,td) ->
                        let uu____891 =
                          let uu____898 =
                            let uu____899 = FStar_Syntax_Subst.compress td in
                            uu____899.FStar_Syntax_Syntax.n in
                          match uu____898 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____908,(t,uu____910)::(d,uu____912)::[]) ->
                              (t, d)
                          | uu____946 -> failwith "Impossibe" in
                        (match uu____891 with
                         | (t,d) ->
                             let uu___217_963 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___217_963.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___217_963.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((Prims.fst lbs), uu____879)
        else lbs in
      let uu____967 = quals_to_string' quals in
      let uu____968 =
        let uu____969 =
          FStar_All.pipe_right (Prims.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____975 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____976 =
                    let uu____977 = FStar_Options.print_universes () in
                    if uu____977
                    then
                      let uu____978 =
                        let uu____979 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____979 ">" in
                      Prims.strcat "<" uu____978
                    else "" in
                  let uu____981 = term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____982 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____975 uu____976
                    uu____981 uu____982)) in
        FStar_Util.concat_l "\n and " uu____969 in
      FStar_Util.format3 "%slet %s %s" uu____967
        (if Prims.fst lbs1 then "rec" else "") uu____968
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____988 = FStar_Options.print_effect_args () in
    if uu____988
    then
      let uu____989 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____989
    else
      (let uu____991 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____992 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____991 uu____992)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.string
  =
  fun s  ->
    fun uu___211_994  ->
      match uu___211_994 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____996 -> s
and binder_to_string':
  Prims.bool ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) -> Prims.string
  =
  fun is_arrow  ->
    fun b  ->
      let uu____1002 = b in
      match uu____1002 with
      | (a,imp) ->
          let uu____1007 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____1007
          then
            let uu____1008 = term_to_string a.FStar_Syntax_Syntax.sort in
            Prims.strcat "_:" uu____1008
          else
            (let uu____1010 =
               (Prims.op_Negation is_arrow) &&
                 (let uu____1011 = FStar_Options.print_bound_var_types () in
                  Prims.op_Negation uu____1011) in
             if uu____1010
             then
               let uu____1012 = nm_to_string a in
               imp_to_string uu____1012 imp
             else
               (let uu____1014 =
                  let uu____1015 = nm_to_string a in
                  let uu____1016 =
                    let uu____1017 =
                      term_to_string a.FStar_Syntax_Syntax.sort in
                    Prims.strcat ":" uu____1017 in
                  Prims.strcat uu____1015 uu____1016 in
                imp_to_string uu____1014 imp))
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
        let uu____1025 = FStar_Options.print_implicits () in
        if uu____1025 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1027 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1027 (FStar_String.concat sep)
      else
        (let uu____1034 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1034 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier Prims.option)
    -> Prims.string
  =
  fun uu___212_1038  ->
    match uu___212_1038 with
    | (a,imp) ->
        let uu____1046 = term_to_string a in imp_to_string uu____1046 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1049 = FStar_Options.print_implicits () in
      if uu____1049 then args else filter_imp args in
    let uu____1053 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1053 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1062) ->
        let uu____1069 =
          let uu____1070 = FStar_Syntax_Subst.compress t in
          uu____1070.FStar_Syntax_Syntax.n in
        (match uu____1069 with
         | FStar_Syntax_Syntax.Tm_type uu____1073 when
             let uu____1074 = FStar_Options.print_implicits () in
             Prims.op_Negation uu____1074 -> term_to_string t
         | uu____1075 ->
             let uu____1076 = term_to_string t in
             FStar_Util.format1 "Tot %s" uu____1076)
    | FStar_Syntax_Syntax.GTotal (t,uu____1078) ->
        let uu____1085 =
          let uu____1086 = FStar_Syntax_Subst.compress t in
          uu____1086.FStar_Syntax_Syntax.n in
        (match uu____1085 with
         | FStar_Syntax_Syntax.Tm_type uu____1089 when
             let uu____1090 = FStar_Options.print_implicits () in
             Prims.op_Negation uu____1090 -> term_to_string t
         | uu____1091 ->
             let uu____1092 = term_to_string t in
             FStar_Util.format1 "GTot %s" uu____1092)
    | FStar_Syntax_Syntax.Comp c1 ->
        let basic =
          let uu____1095 = FStar_Options.print_effect_args () in
          if uu____1095
          then
            let uu____1096 = sli c1.FStar_Syntax_Syntax.effect_name in
            let uu____1097 = term_to_string c1.FStar_Syntax_Syntax.result_typ in
            let uu____1098 =
              let uu____1099 =
                FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map arg_to_string) in
              FStar_All.pipe_right uu____1099 (FStar_String.concat ", ") in
            let uu____1111 =
              let uu____1112 =
                FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                  (FStar_List.map cflags_to_string) in
              FStar_All.pipe_right uu____1112 (FStar_String.concat " ") in
            FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1096
              uu____1097 uu____1098 uu____1111
          else
            (let uu____1118 =
               (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___213_1120  ->
                        match uu___213_1120 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____1121 -> false)))
                 &&
                 (let uu____1122 = FStar_Options.print_effect_args () in
                  Prims.op_Negation uu____1122) in
             if uu____1118
             then
               let uu____1123 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               FStar_Util.format1 "Tot %s" uu____1123
             else
               (let uu____1125 =
                  ((let uu____1126 = FStar_Options.print_effect_args () in
                    Prims.op_Negation uu____1126) &&
                     (let uu____1127 = FStar_Options.print_implicits () in
                      Prims.op_Negation uu____1127))
                    &&
                    (FStar_Ident.lid_equals
                       c1.FStar_Syntax_Syntax.effect_name
                       FStar_Syntax_Const.effect_ML_lid) in
                if uu____1125
                then term_to_string c1.FStar_Syntax_Syntax.result_typ
                else
                  (let uu____1129 =
                     (let uu____1130 = FStar_Options.print_effect_args () in
                      Prims.op_Negation uu____1130) &&
                       (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                          (FStar_Util.for_some
                             (fun uu___214_1132  ->
                                match uu___214_1132 with
                                | FStar_Syntax_Syntax.MLEFFECT  -> true
                                | uu____1133 -> false))) in
                   if uu____1129
                   then
                     let uu____1134 =
                       term_to_string c1.FStar_Syntax_Syntax.result_typ in
                     FStar_Util.format1 "ALL %s" uu____1134
                   else
                     (let uu____1136 = sli c1.FStar_Syntax_Syntax.effect_name in
                      let uu____1137 =
                        term_to_string c1.FStar_Syntax_Syntax.result_typ in
                      FStar_Util.format2 "%s (%s)" uu____1136 uu____1137)))) in
        let dec =
          let uu____1139 =
            FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
              (FStar_List.collect
                 (fun uu___215_1143  ->
                    match uu___215_1143 with
                    | FStar_Syntax_Syntax.DECREASES e ->
                        let uu____1148 =
                          let uu____1149 = term_to_string e in
                          FStar_Util.format1 " (decreases %s)" uu____1149 in
                        [uu____1148]
                    | uu____1150 -> [])) in
          FStar_All.pipe_right uu____1139 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1153 -> ""
and formula_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1160 = FStar_Options.print_universes () in
    if uu____1160 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun uu____1164  ->
    match uu____1164 with
    | (us,t) ->
        let uu____1169 =
          let uu____1170 = univ_names_to_string us in
          FStar_All.pipe_left enclose_universes uu____1170 in
        let uu____1171 = term_to_string t in
        FStar_Util.format2 "%s%s" uu____1169 uu____1171
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  ->
      let actions_to_string actions =
        let uu____1184 =
          FStar_All.pipe_right actions
            (FStar_List.map
               (fun a  ->
                  let uu____1189 = sli a.FStar_Syntax_Syntax.action_name in
                  let uu____1190 =
                    binders_to_string " " a.FStar_Syntax_Syntax.action_params in
                  let uu____1191 =
                    let uu____1192 =
                      univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
                    FStar_All.pipe_left enclose_universes uu____1192 in
                  let uu____1193 =
                    term_to_string a.FStar_Syntax_Syntax.action_typ in
                  let uu____1194 =
                    term_to_string a.FStar_Syntax_Syntax.action_defn in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1189
                    uu____1190 uu____1191 uu____1193 uu____1194)) in
        FStar_All.pipe_right uu____1184 (FStar_String.concat ",\n\t") in
      let uu____1196 =
        let uu____1198 =
          let uu____1200 = lid_to_string ed.FStar_Syntax_Syntax.mname in
          let uu____1201 =
            let uu____1203 =
              let uu____1204 =
                univ_names_to_string ed.FStar_Syntax_Syntax.univs in
              FStar_All.pipe_left enclose_universes uu____1204 in
            let uu____1205 =
              let uu____1207 =
                binders_to_string " " ed.FStar_Syntax_Syntax.binders in
              let uu____1208 =
                let uu____1210 =
                  term_to_string ed.FStar_Syntax_Syntax.signature in
                let uu____1211 =
                  let uu____1213 =
                    tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                  let uu____1214 =
                    let uu____1216 =
                      tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                    let uu____1217 =
                      let uu____1219 =
                        tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else in
                      let uu____1220 =
                        let uu____1222 =
                          tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp in
                        let uu____1223 =
                          let uu____1225 =
                            tscheme_to_string ed.FStar_Syntax_Syntax.stronger in
                          let uu____1226 =
                            let uu____1228 =
                              tscheme_to_string
                                ed.FStar_Syntax_Syntax.close_wp in
                            let uu____1229 =
                              let uu____1231 =
                                tscheme_to_string
                                  ed.FStar_Syntax_Syntax.assert_p in
                              let uu____1232 =
                                let uu____1234 =
                                  tscheme_to_string
                                    ed.FStar_Syntax_Syntax.assume_p in
                                let uu____1235 =
                                  let uu____1237 =
                                    tscheme_to_string
                                      ed.FStar_Syntax_Syntax.null_wp in
                                  let uu____1238 =
                                    let uu____1240 =
                                      tscheme_to_string
                                        ed.FStar_Syntax_Syntax.trivial in
                                    let uu____1241 =
                                      let uu____1243 =
                                        term_to_string
                                          ed.FStar_Syntax_Syntax.repr in
                                      let uu____1244 =
                                        let uu____1246 =
                                          tscheme_to_string
                                            ed.FStar_Syntax_Syntax.bind_repr in
                                        let uu____1247 =
                                          let uu____1249 =
                                            tscheme_to_string
                                              ed.FStar_Syntax_Syntax.return_repr in
                                          let uu____1250 =
                                            let uu____1252 =
                                              actions_to_string
                                                ed.FStar_Syntax_Syntax.actions in
                                            [uu____1252] in
                                          uu____1249 :: uu____1250 in
                                        uu____1246 :: uu____1247 in
                                      uu____1243 :: uu____1244 in
                                    uu____1240 :: uu____1241 in
                                  uu____1237 :: uu____1238 in
                                uu____1234 :: uu____1235 in
                              uu____1231 :: uu____1232 in
                            uu____1228 :: uu____1229 in
                          uu____1225 :: uu____1226 in
                        uu____1222 :: uu____1223 in
                      uu____1219 :: uu____1220 in
                    uu____1216 :: uu____1217 in
                  uu____1213 :: uu____1214 in
                uu____1210 :: uu____1211 in
              uu____1207 :: uu____1208 in
            uu____1203 :: uu____1205 in
          uu____1200 :: uu____1201 in
        (if for_free then "_for_free " else "") :: uu____1198 in
      FStar_Util.format
        "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
        uu____1196
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
        (lid,univs1,tps,k,uu____1263,uu____1264) ->
        let uu____1269 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
        let uu____1270 = binders_to_string " " tps in
        let uu____1271 = term_to_string k in
        FStar_Util.format4 "%stype %s %s : %s" uu____1269 lid.FStar_Ident.str
          uu____1270 uu____1271
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,univs1,t,uu____1275,uu____1276,uu____1277) ->
        let uu____1280 = FStar_Options.print_universes () in
        if uu____1280
        then
          let uu____1281 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          (match uu____1281 with
           | (univs2,t1) ->
               let uu____1286 = univ_names_to_string univs2 in
               let uu____1287 = term_to_string t1 in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____1286
                 lid.FStar_Ident.str uu____1287)
        else
          (let uu____1289 = term_to_string t in
           FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
             uu____1289)
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
        let uu____1293 = FStar_Syntax_Subst.open_univ_vars univs1 t in
        (match uu____1293 with
         | (univs2,t1) ->
             let uu____1298 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let uu____1299 =
               let uu____1300 = FStar_Options.print_universes () in
               if uu____1300
               then
                 let uu____1301 = univ_names_to_string univs2 in
                 FStar_Util.format1 "<%s>" uu____1301
               else "" in
             let uu____1303 = term_to_string t1 in
             FStar_Util.format4 "%sval %s %s : %s" uu____1298
               lid.FStar_Ident.str uu____1299 uu____1303)
    | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
        let uu____1306 = term_to_string f in
        FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1306
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____1308,uu____1309) ->
        lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
    | FStar_Syntax_Syntax.Sig_main e ->
        let uu____1315 = term_to_string e in
        FStar_Util.format1 "let _ = %s" uu____1315
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1317) ->
        let uu____1322 = FStar_List.map sigelt_to_string ses in
        FStar_All.pipe_right uu____1322 (FStar_String.concat "\n")
    | FStar_Syntax_Syntax.Sig_new_effect ed -> eff_decl_to_string false ed
    | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
        eff_decl_to_string true ed
    | FStar_Syntax_Syntax.Sig_sub_effect se ->
        let lift_wp =
          match ((se.FStar_Syntax_Syntax.lift_wp),
                  (se.FStar_Syntax_Syntax.lift))
          with
          | (None ,None ) -> failwith "impossible"
          | (Some lift_wp,uu____1334) -> lift_wp
          | (uu____1338,Some lift) -> lift in
        let uu____1343 =
          FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp)
            (Prims.snd lift_wp) in
        (match uu____1343 with
         | (us,t) ->
             let uu____1350 = lid_to_string se.FStar_Syntax_Syntax.source in
             let uu____1351 = lid_to_string se.FStar_Syntax_Syntax.target in
             let uu____1352 = univ_names_to_string us in
             let uu____1353 = term_to_string t in
             FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1350
               uu____1351 uu____1352 uu____1353)
    | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
        let uu____1361 = FStar_Options.print_universes () in
        if uu____1361
        then
          let uu____1362 =
            let uu____1365 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (tps, c)))
                None FStar_Range.dummyRange in
            FStar_Syntax_Subst.open_univ_vars univs1 uu____1365 in
          (match uu____1362 with
           | (univs2,t) ->
               let uu____1376 =
                 let uu____1384 =
                   let uu____1385 = FStar_Syntax_Subst.compress t in
                   uu____1385.FStar_Syntax_Syntax.n in
                 match uu____1384 with
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                 | uu____1412 -> failwith "impossible" in
               (match uu____1376 with
                | (tps1,c1) ->
                    let uu____1432 = sli l in
                    let uu____1433 = univ_names_to_string univs2 in
                    let uu____1434 = binders_to_string " " tps1 in
                    let uu____1435 = comp_to_string c1 in
                    FStar_Util.format4 "effect %s<%s> %s = %s" uu____1432
                      uu____1433 uu____1434 uu____1435))
        else
          (let uu____1437 = sli l in
           let uu____1438 = binders_to_string " " tps in
           let uu____1439 = comp_to_string c in
           FStar_Util.format3 "effect %s %s = %s" uu____1437 uu____1438
             uu____1439)
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1446 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1446 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1450,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1452;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1454;
                       FStar_Syntax_Syntax.lbdef = uu____1455;_}::[]),uu____1456,uu____1457)
        ->
        let uu____1473 = lbname_to_string lb in
        let uu____1474 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1473 uu____1474
    | uu____1475 ->
        let uu____1476 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1476 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1485 = sli m.FStar_Syntax_Syntax.name in
    let uu____1486 =
      let uu____1487 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1487 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1485 uu____1486
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___216_1492  ->
    match uu___216_1492 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1495 = FStar_Util.string_of_int i in
        let uu____1496 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1495 uu____1496
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1499 = bv_to_string x in
        let uu____1500 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1499 uu____1500
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1507 = bv_to_string x in
        let uu____1508 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1507 uu____1508
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1511 = FStar_Util.string_of_int i in
        let uu____1512 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1511 uu____1512
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1515 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1515
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1519 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1519 (FStar_String.concat "; ")
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
       (let uu____1569 = f x in
        FStar_Util.string_builder_append strb uu____1569);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____1573 = f x1 in
             FStar_Util.string_builder_append strb uu____1573)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____1602 = f x in
        FStar_Util.string_builder_append strb uu____1602);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____1606 = f x1 in
             FStar_Util.string_builder_append strb uu____1606)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)