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
      let uu____1771 = quals_to_string' quals in
      let uu____1772 =
        let uu____1773 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1788 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1789 =
                    let uu____1790 = FStar_Options.print_universes () in
                    if uu____1790
                    then
                      let uu____1791 =
                        let uu____1792 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1792 ">" in
                      Prims.strcat "<" uu____1791
                    else "" in
                  let uu____1794 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1795 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1788 uu____1789
                    uu____1794 uu____1795)) in
        FStar_Util.concat_l "\n and " uu____1773 in
      FStar_Util.format3 "%slet %s %s" uu____1771
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1772
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1802 = FStar_Options.print_effect_args () in
    if uu____1802
    then
      let uu____1803 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1803
    else
      (let uu____1805 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1806 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1805 uu____1806)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___208_1808  ->
      match uu___208_1808 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1811 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1816 =
        let uu____1817 = FStar_Options.ugly () in
        Prims.op_Negation uu____1817 in
      if uu____1816
      then
        let uu____1818 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1818 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1824 = b in
         match uu____1824 with
         | (a,imp) ->
             let uu____1827 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1827
             then
               let uu____1828 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1828
             else
               (let uu____1830 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1832 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1832) in
                if uu____1830
                then
                  let uu____1833 = nm_to_string a in
                  imp_to_string uu____1833 imp
                else
                  (let uu____1835 =
                     let uu____1836 = nm_to_string a in
                     let uu____1837 =
                       let uu____1838 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1838 in
                     Prims.strcat uu____1836 uu____1837 in
                   imp_to_string uu____1835 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1844 = FStar_Options.print_implicits () in
        if uu____1844 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1846 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1846 (FStar_String.concat sep)
      else
        (let uu____1854 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1854 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___209_1861  ->
    match uu___209_1861 with
    | (a,imp) ->
        let uu____1874 = term_to_string a in imp_to_string uu____1874 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1877 = FStar_Options.print_implicits () in
      if uu____1877 then args else filter_imp args in
    let uu____1881 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1881 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1895 =
      let uu____1896 = FStar_Options.ugly () in Prims.op_Negation uu____1896 in
    if uu____1895
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1910 =
             let uu____1911 = FStar_Syntax_Subst.compress t in
             uu____1911.FStar_Syntax_Syntax.n in
           (match uu____1910 with
            | FStar_Syntax_Syntax.Tm_type uu____1914 when
                let uu____1915 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1915 -> term_to_string t
            | uu____1916 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1918 = univ_to_string u in
                     let uu____1919 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1918 uu____1919
                 | uu____1920 ->
                     let uu____1923 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1923))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1934 =
             let uu____1935 = FStar_Syntax_Subst.compress t in
             uu____1935.FStar_Syntax_Syntax.n in
           (match uu____1934 with
            | FStar_Syntax_Syntax.Tm_type uu____1938 when
                let uu____1939 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1939 -> term_to_string t
            | uu____1940 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1942 = univ_to_string u in
                     let uu____1943 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1942 uu____1943
                 | uu____1944 ->
                     let uu____1947 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1947))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1950 = FStar_Options.print_effect_args () in
             if uu____1950
             then
               let uu____1951 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1952 =
                 let uu____1953 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1953 (FStar_String.concat ", ") in
               let uu____1960 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1961 =
                 let uu____1962 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1962 (FStar_String.concat ", ") in
               let uu____1983 =
                 let uu____1984 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1984 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1951
                 uu____1952 uu____1960 uu____1961 uu____1983
             else
               (let uu____1994 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_1998  ->
                           match uu___210_1998 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1999 -> false)))
                    &&
                    (let uu____2001 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2001) in
                if uu____1994
                then
                  let uu____2002 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2002
                else
                  (let uu____2004 =
                     ((let uu____2007 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2007) &&
                        (let uu____2009 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2009))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2004
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2011 =
                        (let uu____2014 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2014) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2018  ->
                                   match uu___211_2018 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2019 -> false))) in
                      if uu____2011
                      then
                        let uu____2020 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2020
                      else
                        (let uu____2022 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2023 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2022 uu____2023)))) in
           let dec =
             let uu____2025 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2035  ->
                       match uu___212_2035 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2041 =
                             let uu____2042 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2042 in
                           [uu____2041]
                       | uu____2043 -> [])) in
             FStar_All.pipe_right uu____2025 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2047 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2057 = b in
    match uu____2057 with
    | (a,imp) ->
        let n1 =
          let uu____2061 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2061
          then FStar_Util.JsonNull
          else
            (let uu____2063 =
               let uu____2064 = nm_to_string a in
               imp_to_string uu____2064 imp in
             FStar_Util.JsonStr uu____2063) in
        let t =
          let uu____2066 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2066 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2083 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2083
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2090 = FStar_Options.print_universes () in
    if uu____2090 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2096 =
      let uu____2097 = FStar_Options.ugly () in Prims.op_Negation uu____2097 in
    if uu____2096
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2101 = s in
       match uu____2101 with
       | (us,t) ->
           let uu____2108 =
             let uu____2109 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2109 in
           let uu____2110 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2108 uu____2110)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2115 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2116 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2117 =
      let uu____2118 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2118 in
    let uu____2119 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2120 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2115 uu____2116 uu____2117
      uu____2119 uu____2120
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
          let uu____2141 =
            let uu____2142 = FStar_Options.ugly () in
            Prims.op_Negation uu____2142 in
          if uu____2141
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2154 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2154 (FStar_String.concat ",\n\t") in
             let uu____2163 =
               let uu____2166 =
                 let uu____2169 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2170 =
                   let uu____2173 =
                     let uu____2174 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2174 in
                   let uu____2175 =
                     let uu____2178 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2179 =
                       let uu____2182 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2183 =
                         let uu____2186 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2187 =
                           let uu____2190 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2191 =
                             let uu____2194 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2195 =
                               let uu____2198 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2199 =
                                 let uu____2202 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2203 =
                                   let uu____2206 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2207 =
                                     let uu____2210 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2211 =
                                       let uu____2214 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2215 =
                                         let uu____2218 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2219 =
                                           let uu____2222 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2223 =
                                             let uu____2226 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2227 =
                                               let uu____2230 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2231 =
                                                 let uu____2234 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2235 =
                                                   let uu____2238 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2238] in
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
                     uu____2178 :: uu____2179 in
                   uu____2173 :: uu____2175 in
                 uu____2169 :: uu____2170 in
               (if for_free then "_for_free " else "") :: uu____2166 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2163)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2252 =
      let uu____2253 = FStar_Options.ugly () in Prims.op_Negation uu____2253 in
    if uu____2252
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2259 -> ""
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
           (lid,univs1,tps,k,uu____2269,uu____2270) ->
           let uu____2279 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2280 = binders_to_string " " tps in
           let uu____2281 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2279
             lid.FStar_Ident.str uu____2280 uu____2281
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2285,uu____2286,uu____2287) ->
           let uu____2292 = FStar_Options.print_universes () in
           if uu____2292
           then
             let uu____2293 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2293 with
              | (univs2,t1) ->
                  let uu____2300 = univ_names_to_string univs2 in
                  let uu____2301 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2300
                    lid.FStar_Ident.str uu____2301)
           else
             (let uu____2303 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2303)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2307 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2307 with
            | (univs2,t1) ->
                let uu____2314 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2315 =
                  let uu____2316 = FStar_Options.print_universes () in
                  if uu____2316
                  then
                    let uu____2317 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2317
                  else "" in
                let uu____2319 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2314
                  lid.FStar_Ident.str uu____2315 uu____2319)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2321,f) ->
           let uu____2323 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2323
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2325) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2331 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2331
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2333) ->
           let uu____2342 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2342 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2360) -> lift_wp
             | (uu____2367,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2375 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2375 with
            | (us,t) ->
                let uu____2386 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2387 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2388 = univ_names_to_string us in
                let uu____2389 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2386
                  uu____2387 uu____2388 uu____2389)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2399 = FStar_Options.print_universes () in
           if uu____2399
           then
             let uu____2400 =
               let uu____2405 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2405 in
             (match uu____2400 with
              | (univs2,t) ->
                  let uu____2408 =
                    let uu____2421 =
                      let uu____2422 = FStar_Syntax_Subst.compress t in
                      uu____2422.FStar_Syntax_Syntax.n in
                    match uu____2421 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2463 -> failwith "impossible" in
                  (match uu____2408 with
                   | (tps1,c1) ->
                       let uu____2494 = sli l in
                       let uu____2495 = univ_names_to_string univs2 in
                       let uu____2496 = binders_to_string " " tps1 in
                       let uu____2497 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2494
                         uu____2495 uu____2496 uu____2497))
           else
             (let uu____2499 = sli l in
              let uu____2500 = binders_to_string " " tps in
              let uu____2501 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2499 uu____2500
                uu____2501))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2510 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2510 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2515,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2517;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2519;
                       FStar_Syntax_Syntax.lbdef = uu____2520;_}::[]),uu____2521)
        ->
        let uu____2544 = lbname_to_string lb in
        let uu____2545 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2544 uu____2545
    | uu____2546 ->
        let uu____2547 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2547 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2562 = sli m.FStar_Syntax_Syntax.name in
    let uu____2563 =
      let uu____2564 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2564 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2562 uu____2563
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___213_2572  ->
    match uu___213_2572 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2575 = FStar_Util.string_of_int i in
        let uu____2576 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2575 uu____2576
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2579 = bv_to_string x in
        let uu____2580 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2579 uu____2580
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2587 = bv_to_string x in
        let uu____2588 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2587 uu____2588
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2591 = FStar_Util.string_of_int i in
        let uu____2592 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2591 uu____2592
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2595 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2595
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2600 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2600 (FStar_String.concat "; ")
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
           (let uu____2672 = f x in
            FStar_Util.string_builder_append strb uu____2672);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2679 = f x1 in
                 FStar_Util.string_builder_append strb uu____2679)) xs;
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
           (let uu____2715 = f x in
            FStar_Util.string_builder_append strb uu____2715);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2722 = f x1 in
                 FStar_Util.string_builder_append strb uu____2722)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)