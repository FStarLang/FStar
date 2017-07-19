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
let infix_prim_ops:
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  [(FStar_Parser_Const.op_Addition, "+");
  (FStar_Parser_Const.op_Subtraction, "-");
  (FStar_Parser_Const.op_Multiply, "*");
  (FStar_Parser_Const.op_Division, "/");
  (FStar_Parser_Const.op_Eq, "=");
  (FStar_Parser_Const.op_ColonEq, ":=");
  (FStar_Parser_Const.op_notEq, "<>");
  (FStar_Parser_Const.op_And, "&&");
  (FStar_Parser_Const.op_Or, "||");
  (FStar_Parser_Const.op_LTE, "<=");
  (FStar_Parser_Const.op_GTE, ">=");
  (FStar_Parser_Const.op_LT, "<");
  (FStar_Parser_Const.op_GT, ">");
  (FStar_Parser_Const.op_Modulus, "mod");
  (FStar_Parser_Const.and_lid, "/\\");
  (FStar_Parser_Const.or_lid, "\\/");
  (FStar_Parser_Const.imp_lid, "==>");
  (FStar_Parser_Const.iff_lid, "<==>");
  (FStar_Parser_Const.precedes_lid, "<<");
  (FStar_Parser_Const.eq2_lid, "==");
  (FStar_Parser_Const.eq3_lid, "===")]
let unary_prim_ops:
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  [(FStar_Parser_Const.op_Negation, "not");
  (FStar_Parser_Const.op_Minus, "-");
  (FStar_Parser_Const.not_lid, "~")]
let is_prim_op ps f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_All.pipe_right ps
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
  | uu____174 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____195 -> failwith "get_lid"
let is_infix_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
let is_unary_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
let quants:
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")]
type exp = FStar_Syntax_Syntax.term
let is_b2t: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Parser_Const.b2t_lid] t
let is_quant: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t
let is_ite: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Parser_Const.ite_lid] t
let is_lex_cons: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Parser_Const.lexcons_lid] f
let is_lex_top: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Parser_Const.lextop_lid] f
let is_inr uu___200_259 =
  match uu___200_259 with
  | FStar_Util.Inl uu____264 -> false
  | FStar_Util.Inr uu____265 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___201_319  ->
          match uu___201_319 with
          | (uu____326,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____327)) -> false
          | uu____330 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____348 =
      let uu____349 = FStar_Syntax_Subst.compress e in
      uu____349.FStar_Syntax_Syntax.n in
    match uu____348 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____436 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____436
        then
          let uu____449 =
            let uu____458 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____458 in
          (match uu____449 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____484 =
                 let uu____491 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____491 :: xs in
               FStar_Pervasives_Native.Some uu____484
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____529 ->
        let uu____530 = is_lex_top e in
        if uu____530
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____581 = f hd1 in if uu____581 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____601 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____601
let infix_prim_op_to_string e =
  let uu____630 = get_lid e in find_lid uu____630 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____646 = get_lid e in find_lid uu____646 unary_prim_ops
let quant_to_string t =
  let uu____662 = get_lid t in find_lid uu____662 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____670) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____675 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____683) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____699 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____699
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___202_702  ->
    match uu___202_702 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____713 = db_to_string x in Prims.strcat "Tm_bvar: " uu____713
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____715 = nm_to_string x in Prims.strcat "Tm_name: " uu____715
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____717 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____717
    | FStar_Syntax_Syntax.Tm_uinst uu____722 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____731 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____732 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____733 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____762 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____777 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____786 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____805 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____836 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____871 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____886 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____903,m) ->
        let uu____973 = FStar_ST.read m in
        (match uu____973 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____992 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____1001 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string u =
  let uu____1021 = FStar_Options.hide_uvar_nums () in
  if uu____1021
  then "?"
  else
    (let uu____1023 =
       let uu____1024 = FStar_Unionfind.uvar_id u in
       FStar_All.pipe_right uu____1024 FStar_Util.string_of_int in
     Prims.strcat "?" uu____1023)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____1037 = FStar_Syntax_Subst.compress_univ u in
      match uu____1037 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____1047 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____1053 =
      let uu____1054 = FStar_Options.ugly () in Prims.op_Negation uu____1054 in
    if uu____1053
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____1058 = FStar_Syntax_Subst.compress_univ u in
       match uu____1058 with
       | FStar_Syntax_Syntax.U_unif u1 -> uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____1068 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____1068
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____1070 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____1070 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____1084 = univ_to_string u2 in
                let uu____1085 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____1084 uu____1085)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____1089 =
             let uu____1090 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____1090 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____1089
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____1102 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____1102 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____1114 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1114 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___203_1122  ->
    match uu___203_1122 with
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
        let uu____1124 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1124
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1127 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1127
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1138 =
          let uu____1139 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1139 in
        let uu____1142 =
          let uu____1143 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1143 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1138 uu____1142
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1162 =
          let uu____1163 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1163 in
        let uu____1166 =
          let uu____1167 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1167 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1162 uu____1166
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1177 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1177
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
    | uu____1186 ->
        let uu____1189 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1189 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1205 ->
        let uu____1208 = quals_to_string quals in Prims.strcat uu____1208 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1266 =
      let uu____1267 = FStar_Options.ugly () in Prims.op_Negation uu____1267 in
    if uu____1266
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1273 = FStar_Options.print_implicits () in
         if uu____1273 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1275 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1314,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1364 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1394 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1409  ->
                                 match uu____1409 with
                                 | (t1,uu____1415) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1394
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1364 (FStar_String.concat "\\/") in
           let uu____1420 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1420
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1440 = tag_of_term t in
           let uu____1441 = sli m in
           let uu____1442 = term_to_string t' in
           let uu____1443 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1440 uu____1441
             uu____1442 uu____1443
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1464 = tag_of_term t in
           let uu____1465 = term_to_string t' in
           let uu____1466 = sli m0 in
           let uu____1467 = sli m1 in
           let uu____1468 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1464
             uu____1465 uu____1466 uu____1467 uu____1468
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1481 = FStar_Range.string_of_range r in
           let uu____1482 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1481
             uu____1482
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1484) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 -> db_to_string x3
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1497) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1530 = FStar_Options.print_universes () in
           if uu____1530
           then
             let uu____1531 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1531
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1555 = binders_to_string " -> " bs in
           let uu____1556 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1555 uu____1556
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some (FStar_Util.Inl l) when
                FStar_Options.print_implicits () ->
                let uu____1621 = binders_to_string " " bs in
                let uu____1622 = term_to_string t2 in
                let uu____1623 =
                  let uu____1624 = l.FStar_Syntax_Syntax.comp () in
                  FStar_All.pipe_left comp_to_string uu____1624 in
                FStar_Util.format3 "(fun %s -> (%s $$ %s))" uu____1621
                  uu____1622 uu____1623
            | FStar_Pervasives_Native.Some (FStar_Util.Inr (l,flags)) when
                FStar_Options.print_implicits () ->
                let uu____1647 = binders_to_string " " bs in
                let uu____1648 = term_to_string t2 in
                FStar_Util.format3 "(fun %s -> (%s $$ (name only) %s))"
                  uu____1647 uu____1648 l.FStar_Ident.str
            | uu____1649 ->
                let uu____1662 = binders_to_string " " bs in
                let uu____1663 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1662 uu____1663)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1674 = bv_to_string xt in
           let uu____1675 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1680 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1674 uu____1675 uu____1680
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1715 = term_to_string t in
           let uu____1716 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1715 uu____1716
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1739 = lbs_to_string [] lbs in
           let uu____1740 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1739 uu____1740
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1829 =
                   let uu____1830 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1830
                     (FStar_Util.dflt "default") in
                 let uu____1835 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1829 uu____1835
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1863 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1863 in
           let uu____1864 = term_to_string e in
           FStar_Util.format3 "(%s <: %s %s)" uu____1864 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1919 = term_to_string head1 in
           let uu____1920 =
             let uu____1921 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1956  ->
                       match uu____1956 with
                       | (p,wopt,e) ->
                           let uu____1972 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1973 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1975 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1975 in
                           let uu____1976 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1972
                             uu____1973 uu____1976)) in
             FStar_Util.concat_l "\n\t|" uu____1921 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1919 uu____1920
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1987 = FStar_Options.print_universes () in
           if uu____1987
           then
             let uu____1988 = term_to_string t in
             let uu____1989 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1988 uu____1989
           else term_to_string t
       | uu____1991 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1993 =
      let uu____1994 = FStar_Options.ugly () in Prims.op_Negation uu____1994 in
    if uu____1993
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2020 = fv_to_string l in
           let uu____2021 =
             let uu____2022 =
               FStar_List.map
                 (fun uu____2029  ->
                    match uu____2029 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____2022 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____2020 uu____2021
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2041) ->
           let uu____2050 = FStar_Options.print_bound_var_types () in
           if uu____2050
           then
             let uu____2051 = bv_to_string x1 in
             let uu____2052 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____2051 uu____2052
           else
             (let uu____2054 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____2054)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2056 = FStar_Options.print_bound_var_types () in
           if uu____2056
           then
             let uu____2057 = bv_to_string x1 in
             let uu____2058 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____2057 uu____2058
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2062 = FStar_Options.print_real_names () in
           if uu____2062
           then
             let uu____2063 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____2063
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____2082 = FStar_Options.print_universes () in
        if uu____2082
        then
          let uu____2089 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____2099 =
                      let uu____2104 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____2104 in
                    match uu____2099 with
                    | (us,td) ->
                        let uu____2107 =
                          let uu____2120 =
                            let uu____2121 = FStar_Syntax_Subst.compress td in
                            uu____2121.FStar_Syntax_Syntax.n in
                          match uu____2120 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____2138,(t,uu____2140)::(d,uu____2142)::[])
                              -> (t, d)
                          | uu____2209 -> failwith "Impossibe" in
                        (match uu____2107 with
                         | (t,d) ->
                             let uu___210_2240 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___210_2240.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___210_2240.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____2089)
        else lbs in
      let uu____2246 = quals_to_string' quals in
      let uu____2247 =
        let uu____2248 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____2258 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____2259 =
                    let uu____2260 = FStar_Options.print_universes () in
                    if uu____2260
                    then
                      let uu____2261 =
                        let uu____2262 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____2262 ">" in
                      Prims.strcat "<" uu____2261
                    else "" in
                  let uu____2264 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____2265 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____2258 uu____2259
                    uu____2264 uu____2265)) in
        FStar_Util.concat_l "\n and " uu____2248 in
      FStar_Util.format3 "%slet %s %s" uu____2246
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____2247
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____2274 = FStar_Options.print_effect_args () in
    if uu____2274
    then
      let uu____2275 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____2275
    else
      (let uu____2277 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____2278 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____2277 uu____2278)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___204_2280  ->
      match uu___204_2280 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____2283 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____2288 =
        let uu____2289 = FStar_Options.ugly () in
        Prims.op_Negation uu____2289 in
      if uu____2288
      then
        let uu____2290 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____2290 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2296 = b in
         match uu____2296 with
         | (a,imp) ->
             let uu____2299 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____2299
             then
               let uu____2300 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____2300
             else
               (let uu____2302 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2303 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____2303) in
                if uu____2302
                then
                  let uu____2304 = nm_to_string a in
                  imp_to_string uu____2304 imp
                else
                  (let uu____2306 =
                     let uu____2307 = nm_to_string a in
                     let uu____2308 =
                       let uu____2309 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____2309 in
                     Prims.strcat uu____2307 uu____2308 in
                   imp_to_string uu____2306 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2315 = FStar_Options.print_implicits () in
        if uu____2315 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____2317 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____2317 (FStar_String.concat sep)
      else
        (let uu____2325 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____2325 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___205_2332  ->
    match uu___205_2332 with
    | (a,imp) ->
        let uu____2345 = term_to_string a in imp_to_string uu____2345 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____2348 = FStar_Options.print_implicits () in
      if uu____2348 then args else filter_imp args in
    let uu____2354 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2354 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____2368 =
      let uu____2369 = FStar_Options.ugly () in Prims.op_Negation uu____2369 in
    if uu____2368
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uu____2374) ->
           let uu____2387 =
             let uu____2388 = FStar_Syntax_Subst.compress t in
             uu____2388.FStar_Syntax_Syntax.n in
           (match uu____2387 with
            | FStar_Syntax_Syntax.Tm_type uu____2393 when
                let uu____2394 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____2394 -> term_to_string t
            | uu____2395 ->
                let uu____2396 = term_to_string t in
                FStar_Util.format1 "Tot %s" uu____2396)
       | FStar_Syntax_Syntax.GTotal (t,uu____2398) ->
           let uu____2411 =
             let uu____2412 = FStar_Syntax_Subst.compress t in
             uu____2412.FStar_Syntax_Syntax.n in
           (match uu____2411 with
            | FStar_Syntax_Syntax.Tm_type uu____2417 when
                let uu____2418 = FStar_Options.print_implicits () in
                Prims.op_Negation uu____2418 -> term_to_string t
            | uu____2419 ->
                let uu____2420 = term_to_string t in
                FStar_Util.format1 "GTot %s" uu____2420)
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2423 = FStar_Options.print_effect_args () in
             if uu____2423
             then
               let uu____2424 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2425 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2426 =
                 let uu____2427 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2427 (FStar_String.concat ", ") in
               let uu____2450 =
                 let uu____2451 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2451 (FStar_String.concat " ") in
               FStar_Util.format4 "%s (%s) %s (attributes %s)" uu____2424
                 uu____2425 uu____2426 uu____2450
             else
               (let uu____2461 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___206_2464  ->
                           match uu___206_2464 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2465 -> false)))
                    &&
                    (let uu____2466 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2466) in
                if uu____2461
                then
                  let uu____2467 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2467
                else
                  (let uu____2469 =
                     ((let uu____2470 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2470) &&
                        (let uu____2471 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2471))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2469
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2473 =
                        (let uu____2474 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2474) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___207_2477  ->
                                   match uu___207_2477 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2478 -> false))) in
                      if uu____2473
                      then
                        let uu____2479 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2479
                      else
                        (let uu____2481 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2482 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2481 uu____2482)))) in
           let dec =
             let uu____2484 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___208_2491  ->
                       match uu___208_2491 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2499 =
                             let uu____2500 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2500 in
                           [uu____2499]
                       | uu____2501 -> [])) in
             FStar_All.pipe_right uu____2484 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2505 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2518 = FStar_Options.print_universes () in
    if uu____2518 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2523 =
      let uu____2524 = FStar_Options.ugly () in Prims.op_Negation uu____2524 in
    if uu____2523
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2528 = s in
       match uu____2528 with
       | (us,t) ->
           let uu____2535 =
             let uu____2536 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2536 in
           let uu____2537 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2535 uu____2537)
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
          let uu____2554 =
            let uu____2555 = FStar_Options.ugly () in
            Prims.op_Negation uu____2555 in
          if uu____2554
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2567 =
                 FStar_All.pipe_right actions
                   (FStar_List.map
                      (fun a  ->
                         let uu____2575 =
                           sli a.FStar_Syntax_Syntax.action_name in
                         let uu____2576 =
                           binders_to_string " "
                             a.FStar_Syntax_Syntax.action_params in
                         let uu____2577 =
                           let uu____2578 =
                             univ_names_to_string
                               a.FStar_Syntax_Syntax.action_univs in
                           FStar_All.pipe_left enclose_universes uu____2578 in
                         let uu____2579 =
                           term_to_string a.FStar_Syntax_Syntax.action_typ in
                         let uu____2580 =
                           term_to_string a.FStar_Syntax_Syntax.action_defn in
                         FStar_Util.format5 "%s%s %s : %s = %s" uu____2575
                           uu____2576 uu____2577 uu____2579 uu____2580)) in
               FStar_All.pipe_right uu____2567 (FStar_String.concat ",\n\t") in
             let uu____2583 =
               let uu____2586 =
                 let uu____2589 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2590 =
                   let uu____2593 =
                     let uu____2594 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2594 in
                   let uu____2595 =
                     let uu____2598 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2599 =
                       let uu____2602 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2603 =
                         let uu____2606 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2607 =
                           let uu____2610 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2611 =
                             let uu____2614 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2615 =
                               let uu____2618 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2619 =
                                 let uu____2622 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2623 =
                                   let uu____2626 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2627 =
                                     let uu____2630 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2631 =
                                       let uu____2634 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2635 =
                                         let uu____2638 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2639 =
                                           let uu____2642 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2643 =
                                             let uu____2646 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2647 =
                                               let uu____2650 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2651 =
                                                 let uu____2654 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2655 =
                                                   let uu____2658 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2658] in
                                                 uu____2654 :: uu____2655 in
                                               uu____2650 :: uu____2651 in
                                             uu____2646 :: uu____2647 in
                                           uu____2642 :: uu____2643 in
                                         uu____2638 :: uu____2639 in
                                       uu____2634 :: uu____2635 in
                                     uu____2630 :: uu____2631 in
                                   uu____2626 :: uu____2627 in
                                 uu____2622 :: uu____2623 in
                               uu____2618 :: uu____2619 in
                             uu____2614 :: uu____2615 in
                           uu____2610 :: uu____2611 in
                         uu____2606 :: uu____2607 in
                       uu____2602 :: uu____2603 in
                     uu____2598 :: uu____2599 in
                   uu____2593 :: uu____2595 in
                 uu____2589 :: uu____2590 in
               (if for_free then "_for_free " else "") :: uu____2586 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2583)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2669 =
      let uu____2670 = FStar_Options.ugly () in Prims.op_Negation uu____2670 in
    if uu____2669
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2676 -> ""
    else
      (match x.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
           "#light \"off\""
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           (FStar_Pervasives_Native.None )) -> "#reset-options"
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
           (FStar_Pervasives_Native.Some s)) ->
           FStar_Util.format1 "#reset-options \"%s\"" s
       | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
           FStar_Util.format1 "#set-options \"%s\"" s
       | FStar_Syntax_Syntax.Sig_inductive_typ
           (lid,univs1,tps,k,uu____2686,uu____2687) ->
           let uu____2696 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2697 = binders_to_string " " tps in
           let uu____2698 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2696
             lid.FStar_Ident.str uu____2697 uu____2698
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2702,uu____2703,uu____2704) ->
           let uu____2709 = FStar_Options.print_universes () in
           if uu____2709
           then
             let uu____2710 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2710 with
              | (univs2,t1) ->
                  let uu____2717 = univ_names_to_string univs2 in
                  let uu____2718 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2717
                    lid.FStar_Ident.str uu____2718)
           else
             (let uu____2720 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2720)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2724 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2724 with
            | (univs2,t1) ->
                let uu____2731 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2732 =
                  let uu____2733 = FStar_Options.print_universes () in
                  if uu____2733
                  then
                    let uu____2734 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2734
                  else "" in
                let uu____2736 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2731
                  lid.FStar_Ident.str uu____2732 uu____2736)
       | FStar_Syntax_Syntax.Sig_assume (lid,f) ->
           let uu____2739 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2739
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2741,uu____2742) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2752 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2752
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2754) ->
           let uu____2763 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2763 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "impossible"
             | (FStar_Pervasives_Native.Some lift_wp,uu____2781) -> lift_wp
             | (uu____2788,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2796 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2796 with
            | (us,t) ->
                let uu____2807 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2808 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2809 = univ_names_to_string us in
                let uu____2810 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2807
                  uu____2808 uu____2809 uu____2810)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2820 = FStar_Options.print_universes () in
           if uu____2820
           then
             let uu____2821 =
               let uu____2826 =
                 (FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_arrow (tps, c)))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2826 in
             (match uu____2821 with
              | (univs2,t) ->
                  let uu____2829 =
                    let uu____2844 =
                      let uu____2845 = FStar_Syntax_Subst.compress t in
                      uu____2845.FStar_Syntax_Syntax.n in
                    match uu____2844 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2896 -> failwith "impossible" in
                  (match uu____2829 with
                   | (tps1,c1) ->
                       let uu____2933 = sli l in
                       let uu____2934 = univ_names_to_string univs2 in
                       let uu____2935 = binders_to_string " " tps1 in
                       let uu____2936 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2933
                         uu____2934 uu____2935 uu____2936))
           else
             (let uu____2938 = sli l in
              let uu____2939 = binders_to_string " " tps in
              let uu____2940 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2938 uu____2939
                uu____2940))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2947 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2947 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2951,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2953;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2955;
                       FStar_Syntax_Syntax.lbdef = uu____2956;_}::[]),uu____2957,uu____2958)
        ->
        let uu____2989 = lbname_to_string lb in
        let uu____2990 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2989 uu____2990
    | uu____2991 ->
        let uu____2992 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2992 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____3005 = sli m.FStar_Syntax_Syntax.name in
    let uu____3006 =
      let uu____3007 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3007 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____3005 uu____3006
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___209_3014  ->
    match uu___209_3014 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____3017 = FStar_Util.string_of_int i in
        let uu____3018 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____3017 uu____3018
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____3021 = bv_to_string x in
        let uu____3022 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____3021 uu____3022
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____3033 = bv_to_string x in
        let uu____3034 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____3033 uu____3034
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____3037 = FStar_Util.string_of_int i in
        let uu____3038 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____3037 uu____3038
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____3041 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____3041
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____3045 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____3045 (FStar_String.concat "; ")
let abs_ascription_to_string:
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
    FStar_Pervasives_Native.option -> Prims.string
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder () in
    (match ascription with
     | FStar_Pervasives_Native.None  ->
         FStar_Util.string_builder_append strb "None"
     | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          FStar_Util.string_builder_append strb
            (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)));
    FStar_Util.string_of_string_builder strb
let list_to_string f elts =
  match elts with
  | [] -> "[]"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "[";
       (let uu____3113 = f x in
        FStar_Util.string_builder_append strb uu____3113);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____3117 = f x1 in
             FStar_Util.string_builder_append strb uu____3117)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____3150 = f x in
        FStar_Util.string_builder_append strb uu____3150);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____3154 = f x1 in
             FStar_Util.string_builder_append strb uu____3154)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)