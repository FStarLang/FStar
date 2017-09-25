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
type exp = FStar_Syntax_Syntax.term[@@deriving show]
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
          let uu____529 = f hd1 in if uu____529 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____551 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____551
let infix_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____574 = get_lid e in find_lid uu____574 infix_prim_ops
let unary_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____583 = get_lid e in find_lid uu____583 unary_prim_ops
let quant_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun t  -> let uu____592 = get_lid t in find_lid uu____592 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (s,uu____601) -> FStar_Util.format1 "\"%s\"" s
    | FStar_Const.Const_bytearray uu____602 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____610) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____626 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____626
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___206_630  ->
    match uu___206_630 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____638 = db_to_string x in Prims.strcat "Tm_bvar: " uu____638
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____640 = nm_to_string x in Prims.strcat "Tm_name: " uu____640
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____642 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____642
    | FStar_Syntax_Syntax.Tm_uinst uu____643 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____650 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____651 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____652 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____669 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____682 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____689 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____704 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____727 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____754 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____767 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____784,m) ->
        let uu____826 = FStar_ST.op_Bang m in
        (match uu____826 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____873 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____878 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____889 = FStar_Options.hide_uvar_nums () in
    if uu____889
    then "?"
    else
      (let uu____891 =
         let uu____892 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____892 FStar_Util.string_of_int in
       Prims.strcat "?" uu____891)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____897 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____898 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____897 uu____898
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____903 = FStar_Options.hide_uvar_nums () in
    if uu____903
    then "?"
    else
      (let uu____905 =
         let uu____906 =
           let uu____907 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____907 FStar_Util.string_of_int in
         let uu____908 =
           let uu____909 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____909 in
         Prims.strcat uu____906 uu____908 in
       Prims.strcat "?" uu____905)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____928 = FStar_Syntax_Subst.compress_univ u in
      match uu____928 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____938 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____945 =
      let uu____946 = FStar_Options.ugly () in Prims.op_Negation uu____946 in
    if uu____945
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____950 = FStar_Syntax_Subst.compress_univ u in
       match uu____950 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____962 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____962
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____964 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____964 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____978 = univ_to_string u2 in
                let uu____979 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____978 uu____979)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____983 =
             let uu____984 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____984 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____983
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____997 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____997 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____1010 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1010 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___207_1020  ->
    match uu___207_1020 with
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
        let uu____1022 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1022
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1025 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1025
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1036 =
          let uu____1037 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1037 in
        let uu____1040 =
          let uu____1041 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1041 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1036 uu____1040
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1060 =
          let uu____1061 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1061 in
        let uu____1064 =
          let uu____1065 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1065 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1060 uu____1064
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1075 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1075
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
    | uu____1085 ->
        let uu____1088 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1088 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1105 ->
        let uu____1108 = quals_to_string quals in Prims.strcat uu____1108 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1164 =
      let uu____1165 = FStar_Options.ugly () in Prims.op_Negation uu____1165 in
    if uu____1164
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1171 = FStar_Options.print_implicits () in
         if uu____1171 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1173 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1198,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1234 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1264 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1282  ->
                                 match uu____1282 with
                                 | (t1,uu____1288) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1264
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1234 (FStar_String.concat "\\/") in
           let uu____1293 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1293
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1305 = tag_of_term t in
           let uu____1306 = sli m in
           let uu____1307 = term_to_string t' in
           let uu____1308 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1305 uu____1306
             uu____1307 uu____1308
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1321 = tag_of_term t in
           let uu____1322 = term_to_string t' in
           let uu____1323 = sli m0 in
           let uu____1324 = sli m1 in
           let uu____1325 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1321
             uu____1322 uu____1323 uu____1324 uu____1325
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1327,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1341 = FStar_Range.string_of_range r in
           let uu____1342 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1341
             uu____1342
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1344) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1350 = db_to_string x3 in
           let uu____1351 =
             let uu____1352 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1352 in
           Prims.strcat uu____1350 uu____1351
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1356) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1383 = FStar_Options.print_universes () in
           if uu____1383
           then
             let uu____1384 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1384
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1404 = binders_to_string " -> " bs in
           let uu____1405 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1404 uu____1405
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1430 = binders_to_string " " bs in
                let uu____1431 = term_to_string t2 in
                let uu____1432 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1436 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1436) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1430 uu____1431
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1432
            | uu____1439 ->
                let uu____1442 = binders_to_string " " bs in
                let uu____1443 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1442 uu____1443)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1450 = bv_to_string xt in
           let uu____1451 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1454 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1450 uu____1451 uu____1454
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1479 = term_to_string t in
           let uu____1480 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1479 uu____1480
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1499 = lbs_to_string [] lbs in
           let uu____1500 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1499 uu____1500
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1561 =
                   let uu____1562 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1562
                     (FStar_Util.dflt "default") in
                 let uu____1567 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1561 uu____1567
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1583 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1583 in
           let uu____1584 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1584 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1623 = term_to_string head1 in
           let uu____1624 =
             let uu____1625 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1661  ->
                       match uu____1661 with
                       | (p,wopt,e) ->
                           let uu____1677 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1678 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1680 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1680 in
                           let uu____1681 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1677
                             uu____1678 uu____1681)) in
             FStar_Util.concat_l "\n\t|" uu____1625 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1623 uu____1624
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1688 = FStar_Options.print_universes () in
           if uu____1688
           then
             let uu____1689 = term_to_string t in
             let uu____1690 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1689 uu____1690
           else term_to_string t
       | uu____1692 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1694 =
      let uu____1695 = FStar_Options.ugly () in Prims.op_Negation uu____1695 in
    if uu____1694
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1717 = fv_to_string l in
           let uu____1718 =
             let uu____1719 =
               FStar_List.map
                 (fun uu____1730  ->
                    match uu____1730 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1719 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1717 uu____1718
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1742) ->
           let uu____1747 = FStar_Options.print_bound_var_types () in
           if uu____1747
           then
             let uu____1748 = bv_to_string x1 in
             let uu____1749 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1748 uu____1749
           else
             (let uu____1751 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1751)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1753 = FStar_Options.print_bound_var_types () in
           if uu____1753
           then
             let uu____1754 = bv_to_string x1 in
             let uu____1755 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1754 uu____1755
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1759 = FStar_Options.print_real_names () in
           if uu____1759
           then
             let uu____1760 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1760
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1772 = quals_to_string' quals in
      let uu____1773 =
        let uu____1774 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1789 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1790 =
                    let uu____1791 = FStar_Options.print_universes () in
                    if uu____1791
                    then
                      let uu____1792 =
                        let uu____1793 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1793 ">" in
                      Prims.strcat "<" uu____1792
                    else "" in
                  let uu____1795 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1796 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1789 uu____1790
                    uu____1795 uu____1796)) in
        FStar_Util.concat_l "\n and " uu____1774 in
      FStar_Util.format3 "%slet %s %s" uu____1772
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1773
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1803 = FStar_Options.print_effect_args () in
    if uu____1803
    then
      let uu____1804 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1804
    else
      (let uu____1806 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1807 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1806 uu____1807)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___208_1809  ->
      match uu___208_1809 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1812 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1817 =
        let uu____1818 = FStar_Options.ugly () in
        Prims.op_Negation uu____1818 in
      if uu____1817
      then
        let uu____1819 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1819 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1825 = b in
         match uu____1825 with
         | (a,imp) ->
             let uu____1828 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1828
             then
               let uu____1829 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1829
             else
               (let uu____1831 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1833 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1833) in
                if uu____1831
                then
                  let uu____1834 = nm_to_string a in
                  imp_to_string uu____1834 imp
                else
                  (let uu____1836 =
                     let uu____1837 = nm_to_string a in
                     let uu____1838 =
                       let uu____1839 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1839 in
                     Prims.strcat uu____1837 uu____1838 in
                   imp_to_string uu____1836 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1845 = FStar_Options.print_implicits () in
        if uu____1845 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1847 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1847 (FStar_String.concat sep)
      else
        (let uu____1855 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1855 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___209_1862  ->
    match uu___209_1862 with
    | (a,imp) ->
        let uu____1875 = term_to_string a in imp_to_string uu____1875 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1878 = FStar_Options.print_implicits () in
      if uu____1878 then args else filter_imp args in
    let uu____1882 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1882 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1896 =
      let uu____1897 = FStar_Options.ugly () in Prims.op_Negation uu____1897 in
    if uu____1896
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1911 =
             let uu____1912 = FStar_Syntax_Subst.compress t in
             uu____1912.FStar_Syntax_Syntax.n in
           (match uu____1911 with
            | FStar_Syntax_Syntax.Tm_type uu____1915 when
                let uu____1916 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1916 -> term_to_string t
            | uu____1917 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1919 = univ_to_string u in
                     let uu____1920 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1919 uu____1920
                 | uu____1921 ->
                     let uu____1924 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1924))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1935 =
             let uu____1936 = FStar_Syntax_Subst.compress t in
             uu____1936.FStar_Syntax_Syntax.n in
           (match uu____1935 with
            | FStar_Syntax_Syntax.Tm_type uu____1939 when
                let uu____1940 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1940 -> term_to_string t
            | uu____1941 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1943 = univ_to_string u in
                     let uu____1944 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1943 uu____1944
                 | uu____1945 ->
                     let uu____1948 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1948))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1951 = FStar_Options.print_effect_args () in
             if uu____1951
             then
               let uu____1952 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1953 =
                 let uu____1954 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1954 (FStar_String.concat ", ") in
               let uu____1961 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1962 =
                 let uu____1963 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1963 (FStar_String.concat ", ") in
               let uu____1984 =
                 let uu____1985 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1985 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1952
                 uu____1953 uu____1961 uu____1962 uu____1984
             else
               (let uu____1995 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_1999  ->
                           match uu___210_1999 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2000 -> false)))
                    &&
                    (let uu____2002 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2002) in
                if uu____1995
                then
                  let uu____2003 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2003
                else
                  (let uu____2005 =
                     ((let uu____2008 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2008) &&
                        (let uu____2010 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2010))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2005
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2012 =
                        (let uu____2015 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2015) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2019  ->
                                   match uu___211_2019 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2020 -> false))) in
                      if uu____2012
                      then
                        let uu____2021 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2021
                      else
                        (let uu____2023 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2024 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2023 uu____2024)))) in
           let dec =
             let uu____2026 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2036  ->
                       match uu___212_2036 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2042 =
                             let uu____2043 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2043 in
                           [uu____2042]
                       | uu____2044 -> [])) in
             FStar_All.pipe_right uu____2026 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2048 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2058 = b in
    match uu____2058 with
    | (a,imp) ->
        let n1 =
          let uu____2062 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2062
          then FStar_Util.JsonNull
          else
            (let uu____2064 =
               let uu____2065 = nm_to_string a in
               imp_to_string uu____2065 imp in
             FStar_Util.JsonStr uu____2064) in
        let t =
          let uu____2067 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2067 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2084 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2084
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2091 = FStar_Options.print_universes () in
    if uu____2091 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2097 =
      let uu____2098 = FStar_Options.ugly () in Prims.op_Negation uu____2098 in
    if uu____2097
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2102 = s in
       match uu____2102 with
       | (us,t) ->
           let uu____2109 =
             let uu____2110 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2110 in
           let uu____2111 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2109 uu____2111)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2116 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2117 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2118 =
      let uu____2119 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2119 in
    let uu____2120 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2121 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2116 uu____2117 uu____2118
      uu____2120 uu____2121
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
          let uu____2142 =
            let uu____2143 = FStar_Options.ugly () in
            Prims.op_Negation uu____2143 in
          if uu____2142
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2155 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2155 (FStar_String.concat ",\n\t") in
             let uu____2164 =
               let uu____2167 =
                 let uu____2170 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2171 =
                   let uu____2174 =
                     let uu____2175 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2175 in
                   let uu____2176 =
                     let uu____2179 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2180 =
                       let uu____2183 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2184 =
                         let uu____2187 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2188 =
                           let uu____2191 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2192 =
                             let uu____2195 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2196 =
                               let uu____2199 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2200 =
                                 let uu____2203 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2204 =
                                   let uu____2207 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2208 =
                                     let uu____2211 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2212 =
                                       let uu____2215 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2216 =
                                         let uu____2219 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2220 =
                                           let uu____2223 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2224 =
                                             let uu____2227 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2228 =
                                               let uu____2231 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2232 =
                                                 let uu____2235 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2236 =
                                                   let uu____2239 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2239] in
                                                 uu____2235 :: uu____2236 in
                                               uu____2231 :: uu____2232 in
                                             uu____2227 :: uu____2228 in
                                           uu____2223 :: uu____2224 in
                                         uu____2219 :: uu____2220 in
                                       uu____2215 :: uu____2216 in
                                     uu____2211 :: uu____2212 in
                                   uu____2207 :: uu____2208 in
                                 uu____2203 :: uu____2204 in
                               uu____2199 :: uu____2200 in
                             uu____2195 :: uu____2196 in
                           uu____2191 :: uu____2192 in
                         uu____2187 :: uu____2188 in
                       uu____2183 :: uu____2184 in
                     uu____2179 :: uu____2180 in
                   uu____2174 :: uu____2176 in
                 uu____2170 :: uu____2171 in
               (if for_free then "_for_free " else "") :: uu____2167 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2164)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2253 =
      let uu____2254 = FStar_Options.ugly () in Prims.op_Negation uu____2254 in
    if uu____2253
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2260 -> ""
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
           (lid,univs1,tps,k,uu____2270,uu____2271) ->
           let uu____2280 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2281 = binders_to_string " " tps in
           let uu____2282 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2280
             lid.FStar_Ident.str uu____2281 uu____2282
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2286,uu____2287,uu____2288) ->
           let uu____2293 = FStar_Options.print_universes () in
           if uu____2293
           then
             let uu____2294 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2294 with
              | (univs2,t1) ->
                  let uu____2301 = univ_names_to_string univs2 in
                  let uu____2302 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2301
                    lid.FStar_Ident.str uu____2302)
           else
             (let uu____2304 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2304)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2308 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2308 with
            | (univs2,t1) ->
                let uu____2315 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2316 =
                  let uu____2317 = FStar_Options.print_universes () in
                  if uu____2317
                  then
                    let uu____2318 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2318
                  else "" in
                let uu____2320 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2315
                  lid.FStar_Ident.str uu____2316 uu____2320)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2322,f) ->
           let uu____2324 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2324
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2326) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2332 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2332
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2334) ->
           let uu____2343 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2343 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2361) -> lift_wp
             | (uu____2368,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2376 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2376 with
            | (us,t) ->
                let uu____2387 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2388 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2389 = univ_names_to_string us in
                let uu____2390 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2387
                  uu____2388 uu____2389 uu____2390)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2400 = FStar_Options.print_universes () in
           if uu____2400
           then
             let uu____2401 =
               let uu____2406 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2406 in
             (match uu____2401 with
              | (univs2,t) ->
                  let uu____2409 =
                    let uu____2422 =
                      let uu____2423 = FStar_Syntax_Subst.compress t in
                      uu____2423.FStar_Syntax_Syntax.n in
                    match uu____2422 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2464 -> failwith "impossible" in
                  (match uu____2409 with
                   | (tps1,c1) ->
                       let uu____2495 = sli l in
                       let uu____2496 = univ_names_to_string univs2 in
                       let uu____2497 = binders_to_string " " tps1 in
                       let uu____2498 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2495
                         uu____2496 uu____2497 uu____2498))
           else
             (let uu____2500 = sli l in
              let uu____2501 = binders_to_string " " tps in
              let uu____2502 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2500 uu____2501
                uu____2502))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2511 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2511 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2516,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2518;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2520;
                       FStar_Syntax_Syntax.lbdef = uu____2521;_}::[]),uu____2522)
        ->
        let uu____2545 = lbname_to_string lb in
        let uu____2546 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2545 uu____2546
    | uu____2547 ->
        let uu____2548 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2548 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2563 = sli m.FStar_Syntax_Syntax.name in
    let uu____2564 =
      let uu____2565 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2565 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2563 uu____2564
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___213_2573  ->
    match uu___213_2573 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2576 = FStar_Util.string_of_int i in
        let uu____2577 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2576 uu____2577
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2580 = bv_to_string x in
        let uu____2581 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2580 uu____2581
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2588 = bv_to_string x in
        let uu____2589 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2588 uu____2589
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2592 = FStar_Util.string_of_int i in
        let uu____2593 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2592 uu____2593
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2596 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2596
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2601 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2601 (FStar_String.concat "; ")
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
           (let uu____2673 = f x in
            FStar_Util.string_builder_append strb uu____2673);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2680 = f x1 in
                 FStar_Util.string_builder_append strb uu____2680)) xs;
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
           (let uu____2716 = f x in
            FStar_Util.string_builder_append strb uu____2716);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2723 = f x1 in
                 FStar_Util.string_builder_append strb uu____2723)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)