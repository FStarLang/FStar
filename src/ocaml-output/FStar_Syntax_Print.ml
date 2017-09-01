open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___197_4  ->
    match uu___197_4 with
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
    let uu____28 =
      let uu____29 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____29 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____28
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____34 = FStar_Options.print_real_names () in
    if uu____34
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____40 =
      let uu____41 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____41 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____40
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
let is_prim_op:
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool
  =
  fun ps  ->
    fun f  ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____177 -> false
let get_lid:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____187 -> failwith "get_lid"
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
let is_inr:
  'Auu____252 'Auu____253 .
    ('Auu____253,'Auu____252) FStar_Util.either -> Prims.bool
  =
  fun uu___198_261  ->
    match uu___198_261 with
    | FStar_Util.Inl uu____266 -> false
    | FStar_Util.Inr uu____267 -> true
let filter_imp:
  'Auu____272 .
    ('Auu____272,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____272,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___199_326  ->
            match uu___199_326 with
            | (uu____333,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____334)) -> false
            | uu____337 -> true))
let rec reconstruct_lex:
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____354 =
      let uu____355 = FStar_Syntax_Subst.compress e in
      uu____355.FStar_Syntax_Syntax.n in
    match uu____354 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____418 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____418
        then
          let uu____427 =
            let uu____434 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____434 in
          (match uu____427 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____452 =
                 let uu____457 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____457 :: xs in
               FStar_Pervasives_Native.Some uu____452
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____481 ->
        let uu____482 = is_lex_top e in
        if uu____482
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find: 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____528 = f hd1 in if uu____528 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____550 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____550
let infix_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____573 = get_lid e in find_lid uu____573 infix_prim_ops
let unary_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____582 = get_lid e in find_lid uu____582 unary_prim_ops
let quant_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun t  -> let uu____591 = get_lid t in find_lid uu____591 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____600) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____605 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____613) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____629 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____629
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___200_633  ->
    match uu___200_633 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____641 = db_to_string x in Prims.strcat "Tm_bvar: " uu____641
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____643 = nm_to_string x in Prims.strcat "Tm_name: " uu____643
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____645 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____645
    | FStar_Syntax_Syntax.Tm_uinst uu____646 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____653 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____654 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____655 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____672 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____685 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____692 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____707 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____730 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____757 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____770 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____787,m) ->
        let uu____829 = FStar_ST.op_Bang m in
        (match uu____829 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____876 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____881 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____892 = FStar_Options.hide_uvar_nums () in
    if uu____892
    then "?"
    else
      (let uu____894 =
         let uu____895 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____895 FStar_Util.string_of_int in
       Prims.strcat "?" uu____894)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____900 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____901 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____900 uu____901
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____906 = FStar_Options.hide_uvar_nums () in
    if uu____906
    then "?"
    else
      (let uu____908 =
         let uu____909 =
           let uu____910 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____910 FStar_Util.string_of_int in
         let uu____911 =
           let uu____912 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____912 in
         Prims.strcat uu____909 uu____911 in
       Prims.strcat "?" uu____908)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____931 = FStar_Syntax_Subst.compress_univ u in
      match uu____931 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____941 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____948 =
      let uu____949 = FStar_Options.ugly () in Prims.op_Negation uu____949 in
    if uu____948
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____953 = FStar_Syntax_Subst.compress_univ u in
       match uu____953 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____965 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____965
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____967 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____967 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____981 = univ_to_string u2 in
                let uu____982 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____981 uu____982)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____986 =
             let uu____987 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____987 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____986
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____1000 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____1000 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____1013 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1013 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___201_1023  ->
    match uu___201_1023 with
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
        let uu____1025 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1025
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1028 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1028
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1039 =
          let uu____1040 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1040 in
        let uu____1043 =
          let uu____1044 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1044 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1039 uu____1043
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1063 =
          let uu____1064 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1064 in
        let uu____1067 =
          let uu____1068 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1068 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1063 uu____1067
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1078 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1078
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
    | uu____1088 ->
        let uu____1091 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1091 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1108 ->
        let uu____1111 = quals_to_string quals in Prims.strcat uu____1111 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1167 =
      let uu____1168 = FStar_Options.ugly () in Prims.op_Negation uu____1168 in
    if uu____1167
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1174 = FStar_Options.print_implicits () in
         if uu____1174 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1176 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1201,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1237 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1267 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1285  ->
                                 match uu____1285 with
                                 | (t1,uu____1291) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1267
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1237 (FStar_String.concat "\\/") in
           let uu____1296 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1296
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1308 = tag_of_term t in
           let uu____1309 = sli m in
           let uu____1310 = term_to_string t' in
           let uu____1311 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1308 uu____1309
             uu____1310 uu____1311
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1324 = tag_of_term t in
           let uu____1325 = term_to_string t' in
           let uu____1326 = sli m0 in
           let uu____1327 = sli m1 in
           let uu____1328 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1324
             uu____1325 uu____1326 uu____1327 uu____1328
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1330,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1344 = FStar_Range.string_of_range r in
           let uu____1345 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1344
             uu____1345
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1347) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1353 = db_to_string x3 in
           let uu____1354 =
             let uu____1355 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1355 in
           Prims.strcat uu____1353 uu____1354
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1359) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1386 = FStar_Options.print_universes () in
           if uu____1386
           then
             let uu____1387 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1387
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1407 = binders_to_string " -> " bs in
           let uu____1408 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1407 uu____1408
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1433 = binders_to_string " " bs in
                let uu____1434 = term_to_string t2 in
                let uu____1435 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1439 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1439) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1433 uu____1434
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1435
            | uu____1442 ->
                let uu____1445 = binders_to_string " " bs in
                let uu____1446 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1445 uu____1446)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1453 = bv_to_string xt in
           let uu____1454 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1457 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1453 uu____1454 uu____1457
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1482 = term_to_string t in
           let uu____1483 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1482 uu____1483
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1502 = lbs_to_string [] lbs in
           let uu____1503 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1502 uu____1503
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1564 =
                   let uu____1565 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1565
                     (FStar_Util.dflt "default") in
                 let uu____1570 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1564 uu____1570
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1586 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1586 in
           let uu____1587 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1587 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1626 = term_to_string head1 in
           let uu____1627 =
             let uu____1628 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1664  ->
                       match uu____1664 with
                       | (p,wopt,e) ->
                           let uu____1680 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1681 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1683 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1683 in
                           let uu____1684 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1680
                             uu____1681 uu____1684)) in
             FStar_Util.concat_l "\n\t|" uu____1628 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1626 uu____1627
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1691 = FStar_Options.print_universes () in
           if uu____1691
           then
             let uu____1692 = term_to_string t in
             let uu____1693 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1692 uu____1693
           else term_to_string t
       | uu____1695 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1697 =
      let uu____1698 = FStar_Options.ugly () in Prims.op_Negation uu____1698 in
    if uu____1697
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1720 = fv_to_string l in
           let uu____1721 =
             let uu____1722 =
               FStar_List.map
                 (fun uu____1733  ->
                    match uu____1733 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1722 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1720 uu____1721
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1745) ->
           let uu____1750 = FStar_Options.print_bound_var_types () in
           if uu____1750
           then
             let uu____1751 = bv_to_string x1 in
             let uu____1752 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1751 uu____1752
           else
             (let uu____1754 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1754)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1756 = FStar_Options.print_bound_var_types () in
           if uu____1756
           then
             let uu____1757 = bv_to_string x1 in
             let uu____1758 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1757 uu____1758
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1762 = FStar_Options.print_real_names () in
           if uu____1762
           then
             let uu____1763 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1763
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1775 = quals_to_string' quals in
      let uu____1776 =
        let uu____1777 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1792 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1793 =
                    let uu____1794 = FStar_Options.print_universes () in
                    if uu____1794
                    then
                      let uu____1795 =
                        let uu____1796 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1796 ">" in
                      Prims.strcat "<" uu____1795
                    else "" in
                  let uu____1798 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1799 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1792 uu____1793
                    uu____1798 uu____1799)) in
        FStar_Util.concat_l "\n and " uu____1777 in
      FStar_Util.format3 "%slet %s %s" uu____1775
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1776
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1806 = FStar_Options.print_effect_args () in
    if uu____1806
    then
      let uu____1807 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1807
    else
      (let uu____1809 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1810 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1809 uu____1810)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___202_1812  ->
      match uu___202_1812 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1815 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1820 =
        let uu____1821 = FStar_Options.ugly () in
        Prims.op_Negation uu____1821 in
      if uu____1820
      then
        let uu____1822 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1822 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1828 = b in
         match uu____1828 with
         | (a,imp) ->
             let uu____1831 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1831
             then
               let uu____1832 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1832
             else
               (let uu____1834 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1836 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1836) in
                if uu____1834
                then
                  let uu____1837 = nm_to_string a in
                  imp_to_string uu____1837 imp
                else
                  (let uu____1839 =
                     let uu____1840 = nm_to_string a in
                     let uu____1841 =
                       let uu____1842 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1842 in
                     Prims.strcat uu____1840 uu____1841 in
                   imp_to_string uu____1839 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1848 = FStar_Options.print_implicits () in
        if uu____1848 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1850 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1850 (FStar_String.concat sep)
      else
        (let uu____1858 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1858 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___203_1865  ->
    match uu___203_1865 with
    | (a,imp) ->
        let uu____1878 = term_to_string a in imp_to_string uu____1878 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1881 = FStar_Options.print_implicits () in
      if uu____1881 then args else filter_imp args in
    let uu____1885 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1885 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1899 =
      let uu____1900 = FStar_Options.ugly () in Prims.op_Negation uu____1900 in
    if uu____1899
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1914 =
             let uu____1915 = FStar_Syntax_Subst.compress t in
             uu____1915.FStar_Syntax_Syntax.n in
           (match uu____1914 with
            | FStar_Syntax_Syntax.Tm_type uu____1918 when
                let uu____1919 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1919 -> term_to_string t
            | uu____1920 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1922 = univ_to_string u in
                     let uu____1923 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1922 uu____1923
                 | uu____1924 ->
                     let uu____1927 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1927))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1938 =
             let uu____1939 = FStar_Syntax_Subst.compress t in
             uu____1939.FStar_Syntax_Syntax.n in
           (match uu____1938 with
            | FStar_Syntax_Syntax.Tm_type uu____1942 when
                let uu____1943 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1943 -> term_to_string t
            | uu____1944 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1946 = univ_to_string u in
                     let uu____1947 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1946 uu____1947
                 | uu____1948 ->
                     let uu____1951 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1951))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1954 = FStar_Options.print_effect_args () in
             if uu____1954
             then
               let uu____1955 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1956 =
                 let uu____1957 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1957 (FStar_String.concat ", ") in
               let uu____1964 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1965 =
                 let uu____1966 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1966 (FStar_String.concat ", ") in
               let uu____1987 =
                 let uu____1988 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1988 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1955
                 uu____1956 uu____1964 uu____1965 uu____1987
             else
               (let uu____1998 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___204_2002  ->
                           match uu___204_2002 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2003 -> false)))
                    &&
                    (let uu____2005 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2005) in
                if uu____1998
                then
                  let uu____2006 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2006
                else
                  (let uu____2008 =
                     ((let uu____2011 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2011) &&
                        (let uu____2013 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2013))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2008
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2015 =
                        (let uu____2018 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2018) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___205_2022  ->
                                   match uu___205_2022 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2023 -> false))) in
                      if uu____2015
                      then
                        let uu____2024 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2024
                      else
                        (let uu____2026 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2027 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2026 uu____2027)))) in
           let dec =
             let uu____2029 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___206_2039  ->
                       match uu___206_2039 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2045 =
                             let uu____2046 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2046 in
                           [uu____2045]
                       | uu____2047 -> [])) in
             FStar_All.pipe_right uu____2029 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2051 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2061 = b in
    match uu____2061 with
    | (a,imp) ->
        let n1 =
          let uu____2065 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2065
          then FStar_Util.JsonNull
          else
            (let uu____2067 =
               let uu____2068 = nm_to_string a in
               imp_to_string uu____2068 imp in
             FStar_Util.JsonStr uu____2067) in
        let t =
          let uu____2070 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2070 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2087 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2087
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2094 = FStar_Options.print_universes () in
    if uu____2094 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2100 =
      let uu____2101 = FStar_Options.ugly () in Prims.op_Negation uu____2101 in
    if uu____2100
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2105 = s in
       match uu____2105 with
       | (us,t) ->
           let uu____2112 =
             let uu____2113 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2113 in
           let uu____2114 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2112 uu____2114)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2119 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2120 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2121 =
      let uu____2122 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2122 in
    let uu____2123 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2124 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2119 uu____2120 uu____2121
      uu____2123 uu____2124
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
          let uu____2145 =
            let uu____2146 = FStar_Options.ugly () in
            Prims.op_Negation uu____2146 in
          if uu____2145
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2158 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2158 (FStar_String.concat ",\n\t") in
             let uu____2167 =
               let uu____2170 =
                 let uu____2173 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2174 =
                   let uu____2177 =
                     let uu____2178 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2178 in
                   let uu____2179 =
                     let uu____2182 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2183 =
                       let uu____2186 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2187 =
                         let uu____2190 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2191 =
                           let uu____2194 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2195 =
                             let uu____2198 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2199 =
                               let uu____2202 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2203 =
                                 let uu____2206 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2207 =
                                   let uu____2210 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2211 =
                                     let uu____2214 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2215 =
                                       let uu____2218 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2219 =
                                         let uu____2222 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2223 =
                                           let uu____2226 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2227 =
                                             let uu____2230 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2231 =
                                               let uu____2234 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2235 =
                                                 let uu____2238 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2239 =
                                                   let uu____2242 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2242] in
                                                 uu____2238 :: uu____2239 in
                                               uu____2234 :: uu____2235 in
                                             uu____2230 :: uu____2231 in
                                           uu____2226 :: uu____2227 in
                                         uu____2222 :: uu____2223 in
                                       uu____2218 :: uu____2219 in
                                     uu____2214 :: uu____2215 in
                                   uu____2210 :: uu____2211 in
                                 uu____2206 :: uu____2207 in
                               uu____2202 :: uu____2203 in
                             uu____2198 :: uu____2199 in
                           uu____2194 :: uu____2195 in
                         uu____2190 :: uu____2191 in
                       uu____2186 :: uu____2187 in
                     uu____2182 :: uu____2183 in
                   uu____2177 :: uu____2179 in
                 uu____2173 :: uu____2174 in
               (if for_free then "_for_free " else "") :: uu____2170 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2167)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2256 =
      let uu____2257 = FStar_Options.ugly () in Prims.op_Negation uu____2257 in
    if uu____2256
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2263 -> ""
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
           (lid,univs1,tps,k,uu____2273,uu____2274) ->
           let uu____2283 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2284 = binders_to_string " " tps in
           let uu____2285 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2283
             lid.FStar_Ident.str uu____2284 uu____2285
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2289,uu____2290,uu____2291) ->
           let uu____2296 = FStar_Options.print_universes () in
           if uu____2296
           then
             let uu____2297 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2297 with
              | (univs2,t1) ->
                  let uu____2304 = univ_names_to_string univs2 in
                  let uu____2305 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2304
                    lid.FStar_Ident.str uu____2305)
           else
             (let uu____2307 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2307)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2311 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2311 with
            | (univs2,t1) ->
                let uu____2318 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2319 =
                  let uu____2320 = FStar_Options.print_universes () in
                  if uu____2320
                  then
                    let uu____2321 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2321
                  else "" in
                let uu____2323 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2318
                  lid.FStar_Ident.str uu____2319 uu____2323)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2325,f) ->
           let uu____2327 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2327
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2329) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2335 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2335
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2337) ->
           let uu____2346 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2346 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2364) -> lift_wp
             | (uu____2371,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2379 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2379 with
            | (us,t) ->
                let uu____2390 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2391 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2392 = univ_names_to_string us in
                let uu____2393 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2390
                  uu____2391 uu____2392 uu____2393)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2403 = FStar_Options.print_universes () in
           if uu____2403
           then
             let uu____2404 =
               let uu____2409 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2409 in
             (match uu____2404 with
              | (univs2,t) ->
                  let uu____2412 =
                    let uu____2425 =
                      let uu____2426 = FStar_Syntax_Subst.compress t in
                      uu____2426.FStar_Syntax_Syntax.n in
                    match uu____2425 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2467 -> failwith "impossible" in
                  (match uu____2412 with
                   | (tps1,c1) ->
                       let uu____2498 = sli l in
                       let uu____2499 = univ_names_to_string univs2 in
                       let uu____2500 = binders_to_string " " tps1 in
                       let uu____2501 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2498
                         uu____2499 uu____2500 uu____2501))
           else
             (let uu____2503 = sli l in
              let uu____2504 = binders_to_string " " tps in
              let uu____2505 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2503 uu____2504
                uu____2505))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2514 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2514 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2519,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2521;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2523;
                       FStar_Syntax_Syntax.lbdef = uu____2524;_}::[]),uu____2525)
        ->
        let uu____2548 = lbname_to_string lb in
        let uu____2549 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2548 uu____2549
    | uu____2550 ->
        let uu____2551 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2551 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2566 = sli m.FStar_Syntax_Syntax.name in
    let uu____2567 =
      let uu____2568 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2568 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2566 uu____2567
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___207_2576  ->
    match uu___207_2576 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2579 = FStar_Util.string_of_int i in
        let uu____2580 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2579 uu____2580
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2583 = bv_to_string x in
        let uu____2584 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2583 uu____2584
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2591 = bv_to_string x in
        let uu____2592 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2591 uu____2592
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2595 = FStar_Util.string_of_int i in
        let uu____2596 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2595 uu____2596
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2599 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2599
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2604 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2604 (FStar_String.concat "; ")
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
let list_to_string:
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "[";
           (let uu____2676 = f x in
            FStar_Util.string_builder_append strb uu____2676);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2683 = f x1 in
                 FStar_Util.string_builder_append strb uu____2683)) xs;
           FStar_Util.string_builder_append strb "]";
           FStar_Util.string_of_string_builder strb)
let set_to_string:
  'a . ('a -> Prims.string) -> 'a FStar_Util.set -> Prims.string =
  fun f  ->
    fun s  ->
      let elts = FStar_Util.set_elements s in
      match elts with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "{";
           (let uu____2719 = f x in
            FStar_Util.string_builder_append strb uu____2719);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2726 = f x1 in
                 FStar_Util.string_builder_append strb uu____2726)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)