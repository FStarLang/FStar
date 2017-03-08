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
let is_inr uu___180_173 =
  match uu___180_173 with
  | FStar_Util.Inl uu____176 -> false
  | FStar_Util.Inr uu____177 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___181_208  ->
          match uu___181_208 with
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
        let args = filter_imp args in
        let exps = FStar_List.map Prims.fst args in
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
  | hd::tl -> let uu____362 = f hd in if uu____362 then hd else find f tl
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
    | FStar_Const.Const_float x -> FStar_Util.string_of_float x
    | FStar_Const.Const_string (bytes,uu____427) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____430 -> "<bytearray>"
    | FStar_Const.Const_int (x,uu____435) -> x
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____445 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____445
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___182_448  ->
    match uu___182_448 with
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
    | FStar_Syntax_Syntax.Tm_let uu____542 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____550 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____559,m) ->
        let uu____597 = FStar_ST.read m in
        (match uu____597 with
         | None  -> "Tm_delayed"
         | Some uu____608 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____613 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string u =
  let uu____627 = FStar_Options.hide_uvar_nums () in
  if uu____627
  then "?"
  else
    (let uu____629 =
       let uu____630 = FStar_Unionfind.uvar_id u in
       FStar_All.pipe_right uu____630 FStar_Util.string_of_int in
     Prims.strcat "?" uu____629)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int* FStar_Syntax_Syntax.universe Prims.option)
  =
  fun n  ->
    fun u  ->
      let uu____640 = FStar_Syntax_Subst.compress_univ u in
      match uu____640 with
      | FStar_Syntax_Syntax.U_zero  -> (n, None)
      | FStar_Syntax_Syntax.U_succ u ->
          int_of_univ (n + (Prims.parse_int "1")) u
      | uu____646 -> (n, (Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____651 = FStar_Syntax_Subst.compress_univ u in
    match uu____651 with
    | FStar_Syntax_Syntax.U_unif u -> uvar_to_string u
    | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____658 = FStar_Util.string_of_int x in
        Prims.strcat "@" uu____658
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u ->
        let uu____660 = int_of_univ (Prims.parse_int "1") u in
        (match uu____660 with
         | (n,None ) -> FStar_Util.string_of_int n
         | (n,Some u) ->
             let uu____669 = univ_to_string u in
             let uu____670 = FStar_Util.string_of_int n in
             FStar_Util.format2 "(%s + %s)" uu____669 uu____670)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____673 =
          let uu____674 = FStar_List.map univ_to_string us in
          FStar_All.pipe_right uu____674 (FStar_String.concat ", ") in
        FStar_Util.format1 "(max %s)" uu____673
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____682 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____682 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____690 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____690 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___183_696  ->
    match uu___183_696 with
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
        let uu____698 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____698
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____701 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____701 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____708 =
          let uu____709 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____709 in
        let uu____711 =
          let uu____712 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____712 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____708 uu____711
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____723 =
          let uu____724 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____724 in
        let uu____726 =
          let uu____727 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____727 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____723 uu____726
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____733 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____733
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
    | uu____740 ->
        let uu____742 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____742 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____752 ->
        let uu____754 = quals_to_string quals in Prims.strcat uu____754 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let x = FStar_Syntax_Subst.compress x in
    let x =
      let uu____810 = FStar_Options.print_implicits () in
      if uu____810 then x else FStar_Syntax_Util.unmeta x in
    match x.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____812 -> failwith "impossible"
    | FStar_Syntax_Syntax.Tm_app (uu____833,[]) -> failwith "Empty args!"
    | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps) ->
        let pats =
          let uu____860 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____876 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____884  ->
                              match uu____884 with
                              | (t,uu____888) -> term_to_string t)) in
                    FStar_All.pipe_right uu____876 (FStar_String.concat "; "))) in
          FStar_All.pipe_right uu____860 (FStar_String.concat "\\/") in
        let uu____891 = term_to_string t in
        FStar_Util.format2 "{:pattern %s} %s" pats uu____891
    | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_monadic (m,t'))
        ->
        let uu____903 = tag_of_term t in
        let uu____904 = sli m in
        let uu____905 = term_to_string t' in
        let uu____906 = term_to_string t in
        FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____903 uu____904
          uu____905 uu____906
    | FStar_Syntax_Syntax.Tm_meta
        (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
        let uu____919 = tag_of_term t in
        let uu____920 = term_to_string t' in
        let uu____921 = sli m0 in
        let uu____922 = sli m1 in
        let uu____923 = term_to_string t in
        FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____919
          uu____920 uu____921 uu____922 uu____923
    | FStar_Syntax_Syntax.Tm_meta
        (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
        FStar_Options.print_implicits () ->
        let uu____932 = FStar_Range.string_of_range r in
        let uu____933 = term_to_string t in
        FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____932 uu____933
    | FStar_Syntax_Syntax.Tm_meta (t,uu____935) -> term_to_string t
    | FStar_Syntax_Syntax.Tm_bvar x -> db_to_string x
    | FStar_Syntax_Syntax.Tm_name x -> nm_to_string x
    | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
    | FStar_Syntax_Syntax.Tm_uvar (u,uu____944) -> uvar_to_string u
    | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
    | FStar_Syntax_Syntax.Tm_type u ->
        let uu____962 = FStar_Options.print_universes () in
        if uu____962
        then
          let uu____963 = univ_to_string u in
          FStar_Util.format1 "Type(%s)" uu____963
        else "Type"
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____977 = binders_to_string " -> " bs in
        let uu____978 = comp_to_string c in
        FStar_Util.format2 "(%s -> %s)" uu____977 uu____978
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
        (match lc with
         | Some (FStar_Util.Inl l) when FStar_Options.print_implicits () ->
             let uu____1013 = binders_to_string " " bs in
             let uu____1014 = term_to_string t2 in
             let uu____1015 =
               let uu____1016 = l.FStar_Syntax_Syntax.comp () in
               FStar_All.pipe_left comp_to_string uu____1016 in
             FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1013
               uu____1014 uu____1015
         | Some (FStar_Util.Inr (l,flags)) when
             FStar_Options.print_implicits () ->
             let uu____1029 = binders_to_string " " bs in
             let uu____1030 = term_to_string t2 in
             FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
               uu____1029 uu____1030 l.FStar_Ident.str
         | uu____1031 ->
             let uu____1038 = binders_to_string " " bs in
             let uu____1039 = term_to_string t2 in
             FStar_Util.format2 "(fun %s -> %s)" uu____1038 uu____1039)
    | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
        let uu____1046 = bv_to_string xt in
        let uu____1047 =
          FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
        let uu____1050 = FStar_All.pipe_right f formula_to_string in
        FStar_Util.format3 "(%s:%s{%s})" uu____1046 uu____1047 uu____1050
    | FStar_Syntax_Syntax.Tm_app (t,args) ->
        let uu____1069 = term_to_string t in
        let uu____1070 = args_to_string args in
        FStar_Util.format2 "(%s %s)" uu____1069 uu____1070
    | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
        let uu____1083 = lbs_to_string [] lbs in
        let uu____1084 = term_to_string e in
        FStar_Util.format2 "%s\nin\n%s" uu____1083 uu____1084
    | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inl t,eff_name) ->
        let uu____1106 = term_to_string e in
        let uu____1107 =
          let uu____1108 =
            FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
          FStar_All.pipe_right uu____1108 (FStar_Util.dflt "default") in
        let uu____1111 = term_to_string t in
        FStar_Util.format3 "(%s <: [%s] %s)" uu____1106 uu____1107 uu____1111
    | FStar_Syntax_Syntax.Tm_ascribed (e,FStar_Util.Inr c,uu____1114) ->
        let uu____1133 = term_to_string e in
        let uu____1134 = comp_to_string c in
        FStar_Util.format2 "(%s <: %s)" uu____1133 uu____1134
    | FStar_Syntax_Syntax.Tm_match (head,branches) ->
        let uu____1163 = term_to_string head in
        let uu____1164 =
          let uu____1165 =
            FStar_All.pipe_right branches
              (FStar_List.map
                 (fun uu____1183  ->
                    match uu____1183 with
                    | (p,wopt,e) ->
                        let uu____1193 = FStar_All.pipe_right p pat_to_string in
                        let uu____1194 =
                          match wopt with
                          | None  -> ""
                          | Some w ->
                              let uu____1196 =
                                FStar_All.pipe_right w term_to_string in
                              FStar_Util.format1 "when %s" uu____1196 in
                        let uu____1197 =
                          FStar_All.pipe_right e term_to_string in
                        FStar_Util.format3 "%s %s -> %s" uu____1193
                          uu____1194 uu____1197)) in
          FStar_Util.concat_l "\n\t|" uu____1165 in
        FStar_Util.format2 "(match %s with\n\t| %s)" uu____1163 uu____1164
    | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
        let uu____1204 = FStar_Options.print_universes () in
        if uu____1204
        then
          let uu____1205 = term_to_string t in
          let uu____1206 = univs_to_string us in
          FStar_Util.format2 "%s<%s>" uu____1205 uu____1206
        else term_to_string t
    | uu____1208 -> tag_of_term x
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
        let uu____1222 = fv_to_string l in
        let uu____1223 =
          let uu____1224 =
            FStar_List.map
              (fun uu____1228  ->
                 match uu____1228 with
                 | (x,b) ->
                     let p = pat_to_string x in
                     if b then Prims.strcat "#" p else p) pats in
          FStar_All.pipe_right uu____1224 (FStar_String.concat " ") in
        FStar_Util.format2 "(%s %s)" uu____1222 uu____1223
    | FStar_Syntax_Syntax.Pat_dot_term (x,uu____1237) ->
        let uu____1242 = FStar_Options.print_bound_var_types () in
        if uu____1242
        then
          let uu____1243 = bv_to_string x in
          let uu____1244 = term_to_string x.FStar_Syntax_Syntax.sort in
          FStar_Util.format2 ".%s:%s" uu____1243 uu____1244
        else
          (let uu____1246 = bv_to_string x in
           FStar_Util.format1 ".%s" uu____1246)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____1248 = FStar_Options.print_bound_var_types () in
        if uu____1248
        then
          let uu____1249 = bv_to_string x in
          let uu____1250 = term_to_string x.FStar_Syntax_Syntax.sort in
          FStar_Util.format2 "%s:%s" uu____1249 uu____1250
        else bv_to_string x
    | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____1254 = FStar_Options.print_real_names () in
        if uu____1254
        then
          let uu____1255 = bv_to_string x in
          Prims.strcat "Pat_wild " uu____1255
        else "_"
    | FStar_Syntax_Syntax.Pat_disj ps ->
        let uu____1261 = FStar_List.map pat_to_string ps in
        FStar_Util.concat_l " | " uu____1261
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs =
        let uu____1273 = FStar_Options.print_universes () in
        if uu____1273
        then
          let uu____1277 =
            FStar_All.pipe_right (Prims.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1283 =
                      let uu____1286 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1286 in
                    match uu____1283 with
                    | (us,td) ->
                        let uu____1289 =
                          let uu____1296 =
                            let uu____1297 = FStar_Syntax_Subst.compress td in
                            uu____1297.FStar_Syntax_Syntax.n in
                          match uu____1296 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1306,(t,uu____1308)::(d,uu____1310)::[])
                              -> (t, d)
                          | uu____1344 -> failwith "Impossibe" in
                        (match uu____1289 with
                         | (t,d) ->
                             let uu___190_1361 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___190_1361.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___190_1361.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((Prims.fst lbs), uu____1277)
        else lbs in
      let uu____1365 = quals_to_string' quals in
      let uu____1366 =
        let uu____1367 =
          FStar_All.pipe_right (Prims.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1373 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1374 =
                    let uu____1375 = FStar_Options.print_universes () in
                    if uu____1375
                    then
                      let uu____1376 =
                        let uu____1377 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1377 ">" in
                      Prims.strcat "<" uu____1376
                    else "" in
                  let uu____1379 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1380 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1373 uu____1374
                    uu____1379 uu____1380)) in
        FStar_Util.concat_l "\n and " uu____1367 in
      FStar_Util.format3 "%slet %s %s" uu____1365
        (if Prims.fst lbs then "rec" else "") uu____1366
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1386 = FStar_Options.print_effect_args () in
    if uu____1386
    then
      let uu____1387 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1387
    else
      (let uu____1389 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1390 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1389 uu____1390)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier Prims.option -> Prims.string
  =
  fun s  ->
    fun uu___184_1392  ->
      match uu___184_1392 with
      | Some (FStar_Syntax_Syntax.Implicit (false )) -> Prims.strcat "#" s
      | Some (FStar_Syntax_Syntax.Implicit (true )) -> Prims.strcat "#." s
      | Some (FStar_Syntax_Syntax.Equality ) -> Prims.strcat "$" s
      | uu____1394 -> s
and binder_to_string':
  Prims.bool ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) -> Prims.string
  =
  fun is_arrow  ->
    fun b  ->
      let uu____1400 = b in
      match uu____1400 with
      | (a,imp) ->
          let uu____1405 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____1405
          then
            let uu____1406 = term_to_string a.FStar_Syntax_Syntax.sort in
            Prims.strcat "_:" uu____1406
          else
            (let uu____1408 =
               (Prims.op_Negation is_arrow) &&
                 (let uu____1409 = FStar_Options.print_bound_var_types () in
                  Prims.op_Negation uu____1409) in
             if uu____1408
             then
               let uu____1410 = nm_to_string a in
               imp_to_string uu____1410 imp
             else
               (let uu____1412 =
                  let uu____1413 = nm_to_string a in
                  let uu____1414 =
                    let uu____1415 =
                      term_to_string a.FStar_Syntax_Syntax.sort in
                    Prims.strcat ":" uu____1415 in
                  Prims.strcat uu____1413 uu____1414 in
                imp_to_string uu____1412 imp))
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
        let uu____1425 = FStar_Options.print_implicits () in
        if uu____1425 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1427 =
          FStar_All.pipe_right bs (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1427 (FStar_String.concat sep)
      else
        (let uu____1434 =
           FStar_All.pipe_right bs (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1434 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.arg_qualifier Prims.option)
    -> Prims.string
  =
  fun uu___185_1440  ->
    match uu___185_1440 with
    | (a,imp) ->
        let uu____1448 = term_to_string a in imp_to_string uu____1448 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args =
      let uu____1451 = FStar_Options.print_implicits () in
      if uu____1451 then args else filter_imp args in
    let uu____1455 = FStar_All.pipe_right args (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1455 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____1464) ->
        let uu____1471 =
          let uu____1472 = FStar_Syntax_Subst.compress t in
          uu____1472.FStar_Syntax_Syntax.n in
        (match uu____1471 with
         | FStar_Syntax_Syntax.Tm_type uu____1475 when
             let uu____1476 = FStar_Options.print_implicits () in
             Prims.op_Negation uu____1476 -> term_to_string t
         | uu____1477 ->
             let uu____1478 = term_to_string t in
             FStar_Util.format1 "Tot %s" uu____1478)
    | FStar_Syntax_Syntax.GTotal (t,uu____1480) ->
        let uu____1487 =
          let uu____1488 = FStar_Syntax_Subst.compress t in
          uu____1488.FStar_Syntax_Syntax.n in
        (match uu____1487 with
         | FStar_Syntax_Syntax.Tm_type uu____1491 when
             let uu____1492 = FStar_Options.print_implicits () in
             Prims.op_Negation uu____1492 -> term_to_string t
         | uu____1493 ->
             let uu____1494 = term_to_string t in
             FStar_Util.format1 "GTot %s" uu____1494)
    | FStar_Syntax_Syntax.Comp c ->
        let basic =
          let uu____1497 = FStar_Options.print_effect_args () in
          if uu____1497
          then
            let uu____1498 = sli c.FStar_Syntax_Syntax.effect_name in
            let uu____1499 = term_to_string c.FStar_Syntax_Syntax.result_typ in
            let uu____1500 =
              let uu____1501 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map arg_to_string) in
              FStar_All.pipe_right uu____1501 (FStar_String.concat ", ") in
            let uu____1513 =
              let uu____1514 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                  (FStar_List.map cflags_to_string) in
              FStar_All.pipe_right uu____1514 (FStar_String.concat " ") in
            FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____1498
              uu____1499 uu____1500 uu____1513
          else
            (let uu____1520 =
               (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___186_1522  ->
                        match uu___186_1522 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | uu____1523 -> false)))
                 &&
                 (let uu____1524 = FStar_Options.print_effect_args () in
                  Prims.op_Negation uu____1524) in
             if uu____1520
             then
               let uu____1525 =
                 term_to_string c.FStar_Syntax_Syntax.result_typ in
               FStar_Util.format1 "Tot %s" uu____1525
             else
               (let uu____1527 =
                  ((let uu____1528 = FStar_Options.print_effect_args () in
                    Prims.op_Negation uu____1528) &&
                     (let uu____1529 = FStar_Options.print_implicits () in
                      Prims.op_Negation uu____1529))
                    &&
                    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.effect_name
                       FStar_Syntax_Const.effect_ML_lid) in
                if uu____1527
                then term_to_string c.FStar_Syntax_Syntax.result_typ
                else
                  (let uu____1531 =
                     (let uu____1532 = FStar_Options.print_effect_args () in
                      Prims.op_Negation uu____1532) &&
                       (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
                          (FStar_Util.for_some
                             (fun uu___187_1534  ->
                                match uu___187_1534 with
                                | FStar_Syntax_Syntax.MLEFFECT  -> true
                                | uu____1535 -> false))) in
                   if uu____1531
                   then
                     let uu____1536 =
                       term_to_string c.FStar_Syntax_Syntax.result_typ in
                     FStar_Util.format1 "ALL %s" uu____1536
                   else
                     (let uu____1538 = sli c.FStar_Syntax_Syntax.effect_name in
                      let uu____1539 =
                        term_to_string c.FStar_Syntax_Syntax.result_typ in
                      FStar_Util.format2 "%s (%s)" uu____1538 uu____1539)))) in
        let dec =
          let uu____1541 =
            FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
              (FStar_List.collect
                 (fun uu___188_1545  ->
                    match uu___188_1545 with
                    | FStar_Syntax_Syntax.DECREASES e ->
                        let uu____1550 =
                          let uu____1551 = term_to_string e in
                          FStar_Util.format1 " (decreases %s)" uu____1551 in
                        [uu____1550]
                    | uu____1552 -> [])) in
          FStar_All.pipe_right uu____1541 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1555 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1564 = FStar_Options.print_universes () in
    if uu____1564 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun uu____1568  ->
    match uu____1568 with
    | (us,t) ->
        let uu____1573 =
          let uu____1574 = univ_names_to_string us in
          FStar_All.pipe_left enclose_universes uu____1574 in
        let uu____1575 = term_to_string t in
        FStar_Util.format2 "%s%s" uu____1573 uu____1575
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  ->
      let actions_to_string actions =
        let uu____1588 =
          FStar_All.pipe_right actions
            (FStar_List.map
               (fun a  ->
                  let uu____1593 = sli a.FStar_Syntax_Syntax.action_name in
                  let uu____1594 =
                    let uu____1595 =
                      univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
                    FStar_All.pipe_left enclose_universes uu____1595 in
                  let uu____1596 =
                    term_to_string a.FStar_Syntax_Syntax.action_typ in
                  let uu____1597 =
                    term_to_string a.FStar_Syntax_Syntax.action_defn in
                  FStar_Util.format4 "%s%s : %s = %s" uu____1593 uu____1594
                    uu____1596 uu____1597)) in
        FStar_All.pipe_right uu____1588 (FStar_String.concat ",\n\t") in
      let uu____1599 =
        let uu____1601 =
          let uu____1603 = lid_to_string ed.FStar_Syntax_Syntax.mname in
          let uu____1604 =
            let uu____1606 =
              let uu____1607 =
                univ_names_to_string ed.FStar_Syntax_Syntax.univs in
              FStar_All.pipe_left enclose_universes uu____1607 in
            let uu____1608 =
              let uu____1610 =
                binders_to_string " " ed.FStar_Syntax_Syntax.binders in
              let uu____1611 =
                let uu____1613 =
                  term_to_string ed.FStar_Syntax_Syntax.signature in
                let uu____1614 =
                  let uu____1616 =
                    tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                  let uu____1617 =
                    let uu____1619 =
                      tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                    let uu____1620 =
                      let uu____1622 =
                        tscheme_to_string ed.FStar_Syntax_Syntax.if_then_else in
                      let uu____1623 =
                        let uu____1625 =
                          tscheme_to_string ed.FStar_Syntax_Syntax.ite_wp in
                        let uu____1626 =
                          let uu____1628 =
                            tscheme_to_string ed.FStar_Syntax_Syntax.stronger in
                          let uu____1629 =
                            let uu____1631 =
                              tscheme_to_string
                                ed.FStar_Syntax_Syntax.close_wp in
                            let uu____1632 =
                              let uu____1634 =
                                tscheme_to_string
                                  ed.FStar_Syntax_Syntax.assert_p in
                              let uu____1635 =
                                let uu____1637 =
                                  tscheme_to_string
                                    ed.FStar_Syntax_Syntax.assume_p in
                                let uu____1638 =
                                  let uu____1640 =
                                    tscheme_to_string
                                      ed.FStar_Syntax_Syntax.null_wp in
                                  let uu____1641 =
                                    let uu____1643 =
                                      tscheme_to_string
                                        ed.FStar_Syntax_Syntax.trivial in
                                    let uu____1644 =
                                      let uu____1646 =
                                        term_to_string
                                          ed.FStar_Syntax_Syntax.repr in
                                      let uu____1647 =
                                        let uu____1649 =
                                          tscheme_to_string
                                            ed.FStar_Syntax_Syntax.bind_repr in
                                        let uu____1650 =
                                          let uu____1652 =
                                            tscheme_to_string
                                              ed.FStar_Syntax_Syntax.return_repr in
                                          let uu____1653 =
                                            let uu____1655 =
                                              actions_to_string
                                                ed.FStar_Syntax_Syntax.actions in
                                            [uu____1655] in
                                          uu____1652 :: uu____1653 in
                                        uu____1649 :: uu____1650 in
                                      uu____1646 :: uu____1647 in
                                    uu____1643 :: uu____1644 in
                                  uu____1640 :: uu____1641 in
                                uu____1637 :: uu____1638 in
                              uu____1634 :: uu____1635 in
                            uu____1631 :: uu____1632 in
                          uu____1628 :: uu____1629 in
                        uu____1625 :: uu____1626 in
                      uu____1622 :: uu____1623 in
                    uu____1619 :: uu____1620 in
                  uu____1616 :: uu____1617 in
                uu____1613 :: uu____1614 in
              uu____1610 :: uu____1611 in
            uu____1606 :: uu____1608 in
          uu____1603 :: uu____1604 in
        (if for_free then "_for_free " else "") :: uu____1601 in
      FStar_Util.format
        "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
        uu____1599
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x with
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.LightOff ,uu____1660) -> "#light \"off\""
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.ResetOptions (None ),uu____1661) ->
        "#reset-options"
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.ResetOptions (Some s),uu____1663) ->
        FStar_Util.format1 "#reset-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.SetOptions s,uu____1665) ->
        FStar_Util.format1 "#set-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_pragma
        (FStar_Syntax_Syntax.LightOff ,uu____1666) -> "#light \"off\""
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,univs,tps,k,uu____1671,uu____1672,quals,uu____1674) ->
        let uu____1681 = quals_to_string' quals in
        let uu____1682 = binders_to_string " " tps in
        let uu____1683 = term_to_string k in
        FStar_Util.format4 "%stype %s %s : %s" uu____1681 lid.FStar_Ident.str
          uu____1682 uu____1683
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,univs,t,uu____1687,uu____1688,uu____1689,uu____1690,uu____1691)
        ->
        let uu____1696 = FStar_Options.print_universes () in
        if uu____1696
        then
          let uu____1697 = FStar_Syntax_Subst.open_univ_vars univs t in
          (match uu____1697 with
           | (univs,t) ->
               let uu____1702 = univ_names_to_string univs in
               let uu____1703 = term_to_string t in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____1702
                 lid.FStar_Ident.str uu____1703)
        else
          (let uu____1705 = term_to_string t in
           FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
             uu____1705)
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs,t,quals,uu____1710) ->
        let uu____1713 = FStar_Syntax_Subst.open_univ_vars univs t in
        (match uu____1713 with
         | (univs,t) ->
             let uu____1718 = quals_to_string' quals in
             let uu____1719 =
               let uu____1720 = FStar_Options.print_universes () in
               if uu____1720
               then
                 let uu____1721 = univ_names_to_string univs in
                 FStar_Util.format1 "<%s>" uu____1721
               else "" in
             let uu____1723 = term_to_string t in
             FStar_Util.format4 "%sval %s %s : %s" uu____1718
               lid.FStar_Ident.str uu____1719 uu____1723)
    | FStar_Syntax_Syntax.Sig_assume (lid,f,uu____1726,uu____1727) ->
        let uu____1730 = term_to_string f in
        FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1730
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____1732,uu____1733,qs,uu____1735)
        -> lbs_to_string qs lbs
    | FStar_Syntax_Syntax.Sig_main (e,uu____1743) ->
        let uu____1744 = term_to_string e in
        FStar_Util.format1 "let _ = %s" uu____1744
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1746,uu____1747,uu____1748)
        ->
        let uu____1755 = FStar_List.map sigelt_to_string ses in
        FStar_All.pipe_right uu____1755 (FStar_String.concat "\n")
    | FStar_Syntax_Syntax.Sig_new_effect (ed,uu____1759) ->
        eff_decl_to_string false ed
    | FStar_Syntax_Syntax.Sig_new_effect_for_free (ed,uu____1761) ->
        eff_decl_to_string true ed
    | FStar_Syntax_Syntax.Sig_sub_effect (se,r) ->
        let lift_wp =
          match ((se.FStar_Syntax_Syntax.lift_wp),
                  (se.FStar_Syntax_Syntax.lift))
          with
          | (None ,None ) -> failwith "impossible"
          | (Some lift_wp,uu____1770) -> lift_wp
          | (uu____1774,Some lift) -> lift in
        let uu____1779 =
          FStar_Syntax_Subst.open_univ_vars (Prims.fst lift_wp)
            (Prims.snd lift_wp) in
        (match uu____1779 with
         | (us,t) ->
             let uu____1786 = lid_to_string se.FStar_Syntax_Syntax.source in
             let uu____1787 = lid_to_string se.FStar_Syntax_Syntax.target in
             let uu____1788 = univ_names_to_string us in
             let uu____1789 = term_to_string t in
             FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1786
               uu____1787 uu____1788 uu____1789)
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (l,univs,tps,c,uu____1794,flags,uu____1796) ->
        let uu____1801 = FStar_Options.print_universes () in
        if uu____1801
        then
          let uu____1802 =
            let uu____1805 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (tps, c)))
                None FStar_Range.dummyRange in
            FStar_Syntax_Subst.open_univ_vars univs uu____1805 in
          (match uu____1802 with
           | (univs,t) ->
               let uu____1816 =
                 let uu____1824 =
                   let uu____1825 = FStar_Syntax_Subst.compress t in
                   uu____1825.FStar_Syntax_Syntax.n in
                 match uu____1824 with
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) -> (bs, c)
                 | uu____1852 -> failwith "impossible" in
               (match uu____1816 with
                | (tps,c) ->
                    let uu____1872 = sli l in
                    let uu____1873 = univ_names_to_string univs in
                    let uu____1874 = binders_to_string " " tps in
                    let uu____1875 = comp_to_string c in
                    FStar_Util.format4 "effect %s<%s> %s = %s" uu____1872
                      uu____1873 uu____1874 uu____1875))
        else
          (let uu____1877 = sli l in
           let uu____1878 = binders_to_string " " tps in
           let uu____1879 = comp_to_string c in
           FStar_Util.format3 "effect %s %s = %s" uu____1877 uu____1878
             uu____1879)
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1886 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1886 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1890,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1892;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1894;
                       FStar_Syntax_Syntax.lbdef = uu____1895;_}::[]),uu____1896,uu____1897,uu____1898,uu____1899)
        ->
        let uu____1917 = lbname_to_string lb in
        let uu____1918 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1917 uu____1918
    | uu____1919 ->
        let uu____1920 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1920 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1929 = sli m.FStar_Syntax_Syntax.name in
    let uu____1930 =
      let uu____1931 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1931 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1929 uu____1930
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___189_1936  ->
    match uu___189_1936 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1939 = FStar_Util.string_of_int i in
        let uu____1940 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1939 uu____1940
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1943 = bv_to_string x in
        let uu____1944 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1943 uu____1944
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1951 = bv_to_string x in
        let uu____1952 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1951 uu____1952
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1955 = FStar_Util.string_of_int i in
        let uu____1956 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1955 uu____1956
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1959 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1959
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1963 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1963 (FStar_String.concat "; ")
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
       (let uu____2013 = f x in
        FStar_Util.string_builder_append strb uu____2013);
       FStar_List.iter
         (fun x  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2017 = f x in
             FStar_Util.string_builder_append strb uu____2017)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2046 = f x in
        FStar_Util.string_builder_append strb uu____2046);
       FStar_List.iter
         (fun x  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2050 = f x in
             FStar_Util.string_builder_append strb uu____2050)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)