open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___203_4  ->
    match uu___203_4 with
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
  fun uu___204_261  ->
    match uu___204_261 with
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
         (fun uu___205_326  ->
            match uu___205_326 with
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
    | FStar_Const.Const_string (s,uu____600) -> FStar_Util.format1 "\"%s\"" s
    | FStar_Const.Const_bytearray uu____601 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____609) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____625 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____625
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___206_629  ->
    match uu___206_629 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____637 = db_to_string x in Prims.strcat "Tm_bvar: " uu____637
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____639 = nm_to_string x in Prims.strcat "Tm_name: " uu____639
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____641 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____641
    | FStar_Syntax_Syntax.Tm_uinst uu____642 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____649 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____650 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____651 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____668 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____681 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____688 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____703 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____726 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____753 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____766 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____783,m) ->
        let uu____825 = FStar_ST.op_Bang m in
        (match uu____825 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____872 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____877 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____888 = FStar_Options.hide_uvar_nums () in
    if uu____888
    then "?"
    else
      (let uu____890 =
         let uu____891 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____891 FStar_Util.string_of_int in
       Prims.strcat "?" uu____890)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____896 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____897 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____896 uu____897
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____902 = FStar_Options.hide_uvar_nums () in
    if uu____902
    then "?"
    else
      (let uu____904 =
         let uu____905 =
           let uu____906 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____906 FStar_Util.string_of_int in
         let uu____907 =
           let uu____908 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____908 in
         Prims.strcat uu____905 uu____907 in
       Prims.strcat "?" uu____904)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____927 = FStar_Syntax_Subst.compress_univ u in
      match uu____927 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____937 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____944 =
      let uu____945 = FStar_Options.ugly () in Prims.op_Negation uu____945 in
    if uu____944
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____949 = FStar_Syntax_Subst.compress_univ u in
       match uu____949 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____961 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____961
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____963 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____963 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____977 = univ_to_string u2 in
                let uu____978 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____977 uu____978)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____982 =
             let uu____983 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____983 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____982
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____996 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____996 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____1009 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1009 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___207_1019  ->
    match uu___207_1019 with
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
        let uu____1021 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1021
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1024 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1024
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1035 =
          let uu____1036 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1036 in
        let uu____1039 =
          let uu____1040 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1040 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1035 uu____1039
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1059 =
          let uu____1060 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1060 in
        let uu____1063 =
          let uu____1064 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1064 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1059 uu____1063
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1074 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1074
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
    | uu____1084 ->
        let uu____1087 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1087 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1104 ->
        let uu____1107 = quals_to_string quals in Prims.strcat uu____1107 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1163 =
      let uu____1164 = FStar_Options.ugly () in Prims.op_Negation uu____1164 in
    if uu____1163
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1170 = FStar_Options.print_implicits () in
         if uu____1170 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1172 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1197,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1233 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1263 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1281  ->
                                 match uu____1281 with
                                 | (t1,uu____1287) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1263
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1233 (FStar_String.concat "\\/") in
           let uu____1292 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1292
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1304 = tag_of_term t in
           let uu____1305 = sli m in
           let uu____1306 = term_to_string t' in
           let uu____1307 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1304 uu____1305
             uu____1306 uu____1307
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1320 = tag_of_term t in
           let uu____1321 = term_to_string t' in
           let uu____1322 = sli m0 in
           let uu____1323 = sli m1 in
           let uu____1324 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1320
             uu____1321 uu____1322 uu____1323 uu____1324
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1326,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1340 = FStar_Range.string_of_range r in
           let uu____1341 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1340
             uu____1341
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1343) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1349 = db_to_string x3 in
           let uu____1350 =
             let uu____1351 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1351 in
           Prims.strcat uu____1349 uu____1350
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1355) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1382 = FStar_Options.print_universes () in
           if uu____1382
           then
             let uu____1383 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1383
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1403 = binders_to_string " -> " bs in
           let uu____1404 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1403 uu____1404
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1429 = binders_to_string " " bs in
                let uu____1430 = term_to_string t2 in
                let uu____1431 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1435 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1435) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1429 uu____1430
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1431
            | uu____1438 ->
                let uu____1441 = binders_to_string " " bs in
                let uu____1442 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1441 uu____1442)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1449 = bv_to_string xt in
           let uu____1450 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1453 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1449 uu____1450 uu____1453
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1478 = term_to_string t in
           let uu____1479 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1478 uu____1479
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1498 = lbs_to_string [] lbs in
           let uu____1499 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1498 uu____1499
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1560 =
                   let uu____1561 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1561
                     (FStar_Util.dflt "default") in
                 let uu____1566 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1560 uu____1566
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1582 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1582 in
           let uu____1583 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1583 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1622 = term_to_string head1 in
           let uu____1623 =
             let uu____1624 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1660  ->
                       match uu____1660 with
                       | (p,wopt,e) ->
                           let uu____1676 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1677 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1679 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1679 in
                           let uu____1680 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1676
                             uu____1677 uu____1680)) in
             FStar_Util.concat_l "\n\t|" uu____1624 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1622 uu____1623
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1687 = FStar_Options.print_universes () in
           if uu____1687
           then
             let uu____1688 = term_to_string t in
             let uu____1689 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1688 uu____1689
           else term_to_string t
       | uu____1691 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1693 =
      let uu____1694 = FStar_Options.ugly () in Prims.op_Negation uu____1694 in
    if uu____1693
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1716 = fv_to_string l in
           let uu____1717 =
             let uu____1718 =
               FStar_List.map
                 (fun uu____1729  ->
                    match uu____1729 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1718 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1716 uu____1717
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1741) ->
           let uu____1746 = FStar_Options.print_bound_var_types () in
           if uu____1746
           then
             let uu____1747 = bv_to_string x1 in
             let uu____1748 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1747 uu____1748
           else
             (let uu____1750 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1750)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1752 = FStar_Options.print_bound_var_types () in
           if uu____1752
           then
             let uu____1753 = bv_to_string x1 in
             let uu____1754 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1753 uu____1754
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1758 = FStar_Options.print_real_names () in
           if uu____1758
           then
             let uu____1759 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1759
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1778 = FStar_Options.print_universes () in
        if uu____1778
        then
          let uu____1785 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1803 =
                      let uu____1808 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1808 in
                    match uu____1803 with
                    | (us,td) ->
                        let uu____1811 =
                          let uu____1820 =
                            let uu____1821 = FStar_Syntax_Subst.compress td in
                            uu____1821.FStar_Syntax_Syntax.n in
                          match uu____1820 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1832,(t,uu____1834)::(d,uu____1836)::[])
                              -> (t, d)
                          | uu____1879 -> failwith "Impossibe" in
                        (match uu____1811 with
                         | (t,d) ->
                             let uu___214_1898 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___214_1898.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___214_1898.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1785)
        else lbs in
      let uu____1904 = quals_to_string' quals in
      let uu____1905 =
        let uu____1906 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1921 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1922 =
                    let uu____1923 = FStar_Options.print_universes () in
                    if uu____1923
                    then
                      let uu____1924 =
                        let uu____1925 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1925 ">" in
                      Prims.strcat "<" uu____1924
                    else "" in
                  let uu____1927 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1928 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1921 uu____1922
                    uu____1927 uu____1928)) in
        FStar_Util.concat_l "\n and " uu____1906 in
      FStar_Util.format3 "%slet %s %s" uu____1904
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1905
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1935 = FStar_Options.print_effect_args () in
    if uu____1935
    then
      let uu____1936 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1936
    else
      (let uu____1938 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1939 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1938 uu____1939)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___208_1941  ->
      match uu___208_1941 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1944 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1949 =
        let uu____1950 = FStar_Options.ugly () in
        Prims.op_Negation uu____1950 in
      if uu____1949
      then
        let uu____1951 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1951 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1957 = b in
         match uu____1957 with
         | (a,imp) ->
             let uu____1960 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1960
             then
               let uu____1961 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1961
             else
               (let uu____1963 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1965 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1965) in
                if uu____1963
                then
                  let uu____1966 = nm_to_string a in
                  imp_to_string uu____1966 imp
                else
                  (let uu____1968 =
                     let uu____1969 = nm_to_string a in
                     let uu____1970 =
                       let uu____1971 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1971 in
                     Prims.strcat uu____1969 uu____1970 in
                   imp_to_string uu____1968 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1977 = FStar_Options.print_implicits () in
        if uu____1977 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1979 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1979 (FStar_String.concat sep)
      else
        (let uu____1987 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1987 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___209_1994  ->
    match uu___209_1994 with
    | (a,imp) ->
        let uu____2007 = term_to_string a in imp_to_string uu____2007 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____2010 = FStar_Options.print_implicits () in
      if uu____2010 then args else filter_imp args in
    let uu____2014 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2014 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____2028 =
      let uu____2029 = FStar_Options.ugly () in Prims.op_Negation uu____2029 in
    if uu____2028
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2043 =
             let uu____2044 = FStar_Syntax_Subst.compress t in
             uu____2044.FStar_Syntax_Syntax.n in
           (match uu____2043 with
            | FStar_Syntax_Syntax.Tm_type uu____2047 when
                let uu____2048 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2048 -> term_to_string t
            | uu____2049 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2051 = univ_to_string u in
                     let uu____2052 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2051 uu____2052
                 | uu____2053 ->
                     let uu____2056 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2056))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2067 =
             let uu____2068 = FStar_Syntax_Subst.compress t in
             uu____2068.FStar_Syntax_Syntax.n in
           (match uu____2067 with
            | FStar_Syntax_Syntax.Tm_type uu____2071 when
                let uu____2072 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2072 -> term_to_string t
            | uu____2073 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2075 = univ_to_string u in
                     let uu____2076 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2075 uu____2076
                 | uu____2077 ->
                     let uu____2080 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2080))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2083 = FStar_Options.print_effect_args () in
             if uu____2083
             then
               let uu____2084 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2085 =
                 let uu____2086 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2086 (FStar_String.concat ", ") in
               let uu____2093 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2094 =
                 let uu____2095 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2095 (FStar_String.concat ", ") in
               let uu____2116 =
                 let uu____2117 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2117 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2084
                 uu____2085 uu____2093 uu____2094 uu____2116
             else
               (let uu____2127 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_2131  ->
                           match uu___210_2131 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2132 -> false)))
                    &&
                    (let uu____2134 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2134) in
                if uu____2127
                then
                  let uu____2135 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2135
                else
                  (let uu____2137 =
                     ((let uu____2140 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2140) &&
                        (let uu____2142 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2142))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2137
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2144 =
                        (let uu____2147 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2147) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2151  ->
                                   match uu___211_2151 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2152 -> false))) in
                      if uu____2144
                      then
                        let uu____2153 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2153
                      else
                        (let uu____2155 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2156 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2155 uu____2156)))) in
           let dec =
             let uu____2158 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2168  ->
                       match uu___212_2168 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2174 =
                             let uu____2175 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2175 in
                           [uu____2174]
                       | uu____2176 -> [])) in
             FStar_All.pipe_right uu____2158 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2180 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2190 = b in
    match uu____2190 with
    | (a,imp) ->
        let n1 =
          let uu____2194 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2194
          then FStar_Util.JsonNull
          else
            (let uu____2196 =
               let uu____2197 = nm_to_string a in
               imp_to_string uu____2197 imp in
             FStar_Util.JsonStr uu____2196) in
        let t =
          let uu____2199 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2199 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2216 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2216
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2223 = FStar_Options.print_universes () in
    if uu____2223 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2229 =
      let uu____2230 = FStar_Options.ugly () in Prims.op_Negation uu____2230 in
    if uu____2229
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2234 = s in
       match uu____2234 with
       | (us,t) ->
           let uu____2241 =
             let uu____2242 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2242 in
           let uu____2243 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2241 uu____2243)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2248 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2249 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2250 =
      let uu____2251 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2251 in
    let uu____2252 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2253 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2248 uu____2249 uu____2250
      uu____2252 uu____2253
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
          let uu____2274 =
            let uu____2275 = FStar_Options.ugly () in
            Prims.op_Negation uu____2275 in
          if uu____2274
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2287 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2287 (FStar_String.concat ",\n\t") in
             let uu____2296 =
               let uu____2299 =
                 let uu____2302 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2303 =
                   let uu____2306 =
                     let uu____2307 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2307 in
                   let uu____2308 =
                     let uu____2311 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2312 =
                       let uu____2315 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2316 =
                         let uu____2319 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2320 =
                           let uu____2323 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2324 =
                             let uu____2327 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2328 =
                               let uu____2331 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2332 =
                                 let uu____2335 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2336 =
                                   let uu____2339 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2340 =
                                     let uu____2343 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2344 =
                                       let uu____2347 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2348 =
                                         let uu____2351 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2352 =
                                           let uu____2355 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2356 =
                                             let uu____2359 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2360 =
                                               let uu____2363 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2364 =
                                                 let uu____2367 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2368 =
                                                   let uu____2371 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2371] in
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
                     uu____2311 :: uu____2312 in
                   uu____2306 :: uu____2308 in
                 uu____2302 :: uu____2303 in
               (if for_free then "_for_free " else "") :: uu____2299 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2296)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2385 =
      let uu____2386 = FStar_Options.ugly () in Prims.op_Negation uu____2386 in
    if uu____2385
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2392 -> ""
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
           (lid,univs1,tps,k,uu____2402,uu____2403) ->
           let uu____2412 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2413 = binders_to_string " " tps in
           let uu____2414 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2412
             lid.FStar_Ident.str uu____2413 uu____2414
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2418,uu____2419,uu____2420) ->
           let uu____2425 = FStar_Options.print_universes () in
           if uu____2425
           then
             let uu____2426 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2426 with
              | (univs2,t1) ->
                  let uu____2433 = univ_names_to_string univs2 in
                  let uu____2434 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2433
                    lid.FStar_Ident.str uu____2434)
           else
             (let uu____2436 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2436)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2440 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2440 with
            | (univs2,t1) ->
                let uu____2447 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2448 =
                  let uu____2449 = FStar_Options.print_universes () in
                  if uu____2449
                  then
                    let uu____2450 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2450
                  else "" in
                let uu____2452 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2447
                  lid.FStar_Ident.str uu____2448 uu____2452)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2454,f) ->
           let uu____2456 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2456
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2458) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2464 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2464
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2466) ->
           let uu____2475 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2475 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2493) -> lift_wp
             | (uu____2500,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2508 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2508 with
            | (us,t) ->
                let uu____2519 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2520 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2521 = univ_names_to_string us in
                let uu____2522 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2519
                  uu____2520 uu____2521 uu____2522)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2532 = FStar_Options.print_universes () in
           if uu____2532
           then
             let uu____2533 =
               let uu____2538 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2538 in
             (match uu____2533 with
              | (univs2,t) ->
                  let uu____2541 =
                    let uu____2554 =
                      let uu____2555 = FStar_Syntax_Subst.compress t in
                      uu____2555.FStar_Syntax_Syntax.n in
                    match uu____2554 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2596 -> failwith "impossible" in
                  (match uu____2541 with
                   | (tps1,c1) ->
                       let uu____2627 = sli l in
                       let uu____2628 = univ_names_to_string univs2 in
                       let uu____2629 = binders_to_string " " tps1 in
                       let uu____2630 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2627
                         uu____2628 uu____2629 uu____2630))
           else
             (let uu____2632 = sli l in
              let uu____2633 = binders_to_string " " tps in
              let uu____2634 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2632 uu____2633
                uu____2634))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2643 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2643 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2648,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2650;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2652;
                       FStar_Syntax_Syntax.lbdef = uu____2653;_}::[]),uu____2654)
        ->
        let uu____2677 = lbname_to_string lb in
        let uu____2678 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2677 uu____2678
    | uu____2679 ->
        let uu____2680 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2680 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2695 = sli m.FStar_Syntax_Syntax.name in
    let uu____2696 =
      let uu____2697 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2697 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2695 uu____2696
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___213_2705  ->
    match uu___213_2705 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2708 = FStar_Util.string_of_int i in
        let uu____2709 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2708 uu____2709
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2712 = bv_to_string x in
        let uu____2713 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2712 uu____2713
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2720 = bv_to_string x in
        let uu____2721 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2720 uu____2721
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2724 = FStar_Util.string_of_int i in
        let uu____2725 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2724 uu____2725
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2728 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2728
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2733 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2733 (FStar_String.concat "; ")
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
           (let uu____2805 = f x in
            FStar_Util.string_builder_append strb uu____2805);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2812 = f x1 in
                 FStar_Util.string_builder_append strb uu____2812)) xs;
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
           (let uu____2848 = f x in
            FStar_Util.string_builder_append strb uu____2848);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2855 = f x1 in
                 FStar_Util.string_builder_append strb uu____2855)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)