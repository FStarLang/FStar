open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___199_4  ->
    match uu___199_4 with
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
  fun uu___200_261  ->
    match uu___200_261 with
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
         (fun uu___201_326  ->
            match uu___201_326 with
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
  fun uu___202_633  ->
    match uu___202_633 with
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
  fun uu___203_1023  ->
    match uu___203_1023 with
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
      let lbs1 =
        let uu____1782 = FStar_Options.print_universes () in
        if uu____1782
        then
          let uu____1789 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1807 =
                      let uu____1812 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1812 in
                    match uu____1807 with
                    | (us,td) ->
                        let uu____1815 =
                          let uu____1824 =
                            let uu____1825 = FStar_Syntax_Subst.compress td in
                            uu____1825.FStar_Syntax_Syntax.n in
                          match uu____1824 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1836,(t,uu____1838)::(d,uu____1840)::[])
                              -> (t, d)
                          | uu____1883 -> failwith "Impossibe" in
                        (match uu____1815 with
                         | (t,d) ->
                             let uu___210_1902 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___210_1902.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___210_1902.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1789)
        else lbs in
      let uu____1908 = quals_to_string' quals in
      let uu____1909 =
        let uu____1910 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1925 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1926 =
                    let uu____1927 = FStar_Options.print_universes () in
                    if uu____1927
                    then
                      let uu____1928 =
                        let uu____1929 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1929 ">" in
                      Prims.strcat "<" uu____1928
                    else "" in
                  let uu____1931 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1932 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1925 uu____1926
                    uu____1931 uu____1932)) in
        FStar_Util.concat_l "\n and " uu____1910 in
      FStar_Util.format3 "%slet %s %s" uu____1908
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1909
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1939 = FStar_Options.print_effect_args () in
    if uu____1939
    then
      let uu____1940 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1940
    else
      (let uu____1942 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1943 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1942 uu____1943)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___204_1945  ->
      match uu___204_1945 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1948 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1953 =
        let uu____1954 = FStar_Options.ugly () in
        Prims.op_Negation uu____1954 in
      if uu____1953
      then
        let uu____1955 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1955 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1961 = b in
         match uu____1961 with
         | (a,imp) ->
             let uu____1964 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1964
             then
               let uu____1965 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1965
             else
               (let uu____1967 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1969 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1969) in
                if uu____1967
                then
                  let uu____1970 = nm_to_string a in
                  imp_to_string uu____1970 imp
                else
                  (let uu____1972 =
                     let uu____1973 = nm_to_string a in
                     let uu____1974 =
                       let uu____1975 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1975 in
                     Prims.strcat uu____1973 uu____1974 in
                   imp_to_string uu____1972 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1981 = FStar_Options.print_implicits () in
        if uu____1981 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1983 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1983 (FStar_String.concat sep)
      else
        (let uu____1991 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1991 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___205_1998  ->
    match uu___205_1998 with
    | (a,imp) ->
        let uu____2011 = term_to_string a in imp_to_string uu____2011 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____2014 = FStar_Options.print_implicits () in
      if uu____2014 then args else filter_imp args in
    let uu____2018 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2018 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____2032 =
      let uu____2033 = FStar_Options.ugly () in Prims.op_Negation uu____2033 in
    if uu____2032
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2047 =
             let uu____2048 = FStar_Syntax_Subst.compress t in
             uu____2048.FStar_Syntax_Syntax.n in
           (match uu____2047 with
            | FStar_Syntax_Syntax.Tm_type uu____2051 when
                let uu____2052 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2052 -> term_to_string t
            | uu____2053 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2055 = univ_to_string u in
                     let uu____2056 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2055 uu____2056
                 | uu____2057 ->
                     let uu____2060 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2060))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2071 =
             let uu____2072 = FStar_Syntax_Subst.compress t in
             uu____2072.FStar_Syntax_Syntax.n in
           (match uu____2071 with
            | FStar_Syntax_Syntax.Tm_type uu____2075 when
                let uu____2076 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2076 -> term_to_string t
            | uu____2077 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2079 = univ_to_string u in
                     let uu____2080 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2079 uu____2080
                 | uu____2081 ->
                     let uu____2084 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2084))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2087 = FStar_Options.print_effect_args () in
             if uu____2087
             then
               let uu____2088 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2089 =
                 let uu____2090 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2090 (FStar_String.concat ", ") in
               let uu____2097 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2098 =
                 let uu____2099 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2099 (FStar_String.concat ", ") in
               let uu____2120 =
                 let uu____2121 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2121 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2088
                 uu____2089 uu____2097 uu____2098 uu____2120
             else
               (let uu____2131 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___206_2135  ->
                           match uu___206_2135 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2136 -> false)))
                    &&
                    (let uu____2138 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2138) in
                if uu____2131
                then
                  let uu____2139 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2139
                else
                  (let uu____2141 =
                     ((let uu____2144 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2144) &&
                        (let uu____2146 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2146))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2141
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2148 =
                        (let uu____2151 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2151) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___207_2155  ->
                                   match uu___207_2155 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2156 -> false))) in
                      if uu____2148
                      then
                        let uu____2157 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2157
                      else
                        (let uu____2159 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2160 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2159 uu____2160)))) in
           let dec =
             let uu____2162 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___208_2172  ->
                       match uu___208_2172 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2178 =
                             let uu____2179 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2179 in
                           [uu____2178]
                       | uu____2180 -> [])) in
             FStar_All.pipe_right uu____2162 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2184 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2194 = b in
    match uu____2194 with
    | (a,imp) ->
        let n1 =
          let uu____2198 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2198
          then FStar_Util.JsonNull
          else
            (let uu____2200 =
               let uu____2201 = nm_to_string a in
               imp_to_string uu____2201 imp in
             FStar_Util.JsonStr uu____2200) in
        let t =
          let uu____2203 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2203 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2220 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2220
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2227 = FStar_Options.print_universes () in
    if uu____2227 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2233 =
      let uu____2234 = FStar_Options.ugly () in Prims.op_Negation uu____2234 in
    if uu____2233
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2238 = s in
       match uu____2238 with
       | (us,t) ->
           let uu____2245 =
             let uu____2246 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2246 in
           let uu____2247 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2245 uu____2247)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2252 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2253 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2254 =
      let uu____2255 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2255 in
    let uu____2256 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2257 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2252 uu____2253 uu____2254
      uu____2256 uu____2257
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
          let uu____2278 =
            let uu____2279 = FStar_Options.ugly () in
            Prims.op_Negation uu____2279 in
          if uu____2278
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2291 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2291 (FStar_String.concat ",\n\t") in
             let uu____2300 =
               let uu____2303 =
                 let uu____2306 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2307 =
                   let uu____2310 =
                     let uu____2311 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2311 in
                   let uu____2312 =
                     let uu____2315 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2316 =
                       let uu____2319 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2320 =
                         let uu____2323 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2324 =
                           let uu____2327 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2328 =
                             let uu____2331 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2332 =
                               let uu____2335 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2336 =
                                 let uu____2339 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2340 =
                                   let uu____2343 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2344 =
                                     let uu____2347 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2348 =
                                       let uu____2351 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2352 =
                                         let uu____2355 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2356 =
                                           let uu____2359 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2360 =
                                             let uu____2363 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2364 =
                                               let uu____2367 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2368 =
                                                 let uu____2371 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2372 =
                                                   let uu____2375 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2375] in
                                                 uu____2371 :: uu____2372 in
                                               uu____2367 :: uu____2368 in
                                             uu____2363 :: uu____2364 in
                                           uu____2359 :: uu____2360 in
                                         uu____2355 :: uu____2356 in
                                       uu____2351 :: uu____2352 in
                                     uu____2347 :: uu____2348 in
                                   uu____2343 :: uu____2344 in
                                 uu____2339 :: uu____2340 in
                               uu____2335 :: uu____2336 in
                             uu____2331 :: uu____2332 in
                           uu____2327 :: uu____2328 in
                         uu____2323 :: uu____2324 in
                       uu____2319 :: uu____2320 in
                     uu____2315 :: uu____2316 in
                   uu____2310 :: uu____2312 in
                 uu____2306 :: uu____2307 in
               (if for_free then "_for_free " else "") :: uu____2303 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2300)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2389 =
      let uu____2390 = FStar_Options.ugly () in Prims.op_Negation uu____2390 in
    if uu____2389
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2396 -> ""
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
           (lid,univs1,tps,k,uu____2406,uu____2407) ->
           let uu____2416 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2417 = binders_to_string " " tps in
           let uu____2418 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2416
             lid.FStar_Ident.str uu____2417 uu____2418
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2422,uu____2423,uu____2424) ->
           let uu____2429 = FStar_Options.print_universes () in
           if uu____2429
           then
             let uu____2430 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2430 with
              | (univs2,t1) ->
                  let uu____2437 = univ_names_to_string univs2 in
                  let uu____2438 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2437
                    lid.FStar_Ident.str uu____2438)
           else
             (let uu____2440 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2440)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2444 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2444 with
            | (univs2,t1) ->
                let uu____2451 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2452 =
                  let uu____2453 = FStar_Options.print_universes () in
                  if uu____2453
                  then
                    let uu____2454 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2454
                  else "" in
                let uu____2456 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2451
                  lid.FStar_Ident.str uu____2452 uu____2456)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2458,f) ->
           let uu____2460 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2460
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2462) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2468 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2468
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2470) ->
           let uu____2479 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2479 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2497) -> lift_wp
             | (uu____2504,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2512 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2512 with
            | (us,t) ->
                let uu____2523 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2524 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2525 = univ_names_to_string us in
                let uu____2526 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2523
                  uu____2524 uu____2525 uu____2526)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2536 = FStar_Options.print_universes () in
           if uu____2536
           then
             let uu____2537 =
               let uu____2542 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2542 in
             (match uu____2537 with
              | (univs2,t) ->
                  let uu____2545 =
                    let uu____2558 =
                      let uu____2559 = FStar_Syntax_Subst.compress t in
                      uu____2559.FStar_Syntax_Syntax.n in
                    match uu____2558 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2600 -> failwith "impossible" in
                  (match uu____2545 with
                   | (tps1,c1) ->
                       let uu____2631 = sli l in
                       let uu____2632 = univ_names_to_string univs2 in
                       let uu____2633 = binders_to_string " " tps1 in
                       let uu____2634 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2631
                         uu____2632 uu____2633 uu____2634))
           else
             (let uu____2636 = sli l in
              let uu____2637 = binders_to_string " " tps in
              let uu____2638 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2636 uu____2637
                uu____2638))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2647 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2647 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2652,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2654;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2656;
                       FStar_Syntax_Syntax.lbdef = uu____2657;_}::[]),uu____2658)
        ->
        let uu____2681 = lbname_to_string lb in
        let uu____2682 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2681 uu____2682
    | uu____2683 ->
        let uu____2684 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2684 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2699 = sli m.FStar_Syntax_Syntax.name in
    let uu____2700 =
      let uu____2701 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2701 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2699 uu____2700
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___209_2709  ->
    match uu___209_2709 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2712 = FStar_Util.string_of_int i in
        let uu____2713 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2712 uu____2713
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2716 = bv_to_string x in
        let uu____2717 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2716 uu____2717
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2724 = bv_to_string x in
        let uu____2725 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2724 uu____2725
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2728 = FStar_Util.string_of_int i in
        let uu____2729 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2728 uu____2729
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2732 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2732
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2737 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2737 (FStar_String.concat "; ")
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
           (let uu____2809 = f x in
            FStar_Util.string_builder_append strb uu____2809);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2816 = f x1 in
                 FStar_Util.string_builder_append strb uu____2816)) xs;
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
           (let uu____2852 = f x in
            FStar_Util.string_builder_append strb uu____2852);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2859 = f x1 in
                 FStar_Util.string_builder_append strb uu____2859)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)