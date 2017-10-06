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
        let uu____634 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____634
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___206_638  ->
    match uu___206_638 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____646 = db_to_string x in Prims.strcat "Tm_bvar: " uu____646
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____648 = nm_to_string x in Prims.strcat "Tm_name: " uu____648
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____650 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____650
    | FStar_Syntax_Syntax.Tm_uinst uu____651 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____658 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____659 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____660 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____677 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____690 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____697 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____712 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____735 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____762 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____775 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____792,m) ->
        let uu____834 = FStar_ST.op_Bang m in
        (match uu____834 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____909 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____914 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____925 = FStar_Options.hide_uvar_nums () in
    if uu____925
    then "?"
    else
      (let uu____927 =
         let uu____928 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____928 FStar_Util.string_of_int in
       Prims.strcat "?" uu____927)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____933 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____934 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____933 uu____934
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____939 = FStar_Options.hide_uvar_nums () in
    if uu____939
    then "?"
    else
      (let uu____941 =
         let uu____942 =
           let uu____943 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____943 FStar_Util.string_of_int in
         let uu____944 =
           let uu____945 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____945 in
         Prims.strcat uu____942 uu____944 in
       Prims.strcat "?" uu____941)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____964 = FStar_Syntax_Subst.compress_univ u in
      match uu____964 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____974 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____981 =
      let uu____982 = FStar_Options.ugly () in Prims.op_Negation uu____982 in
    if uu____981
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____986 = FStar_Syntax_Subst.compress_univ u in
       match uu____986 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____998 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____998
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____1000 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____1000 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____1014 = univ_to_string u2 in
                let uu____1015 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____1014 uu____1015)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____1019 =
             let uu____1020 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____1020 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____1019
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____1033 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____1033 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____1046 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1046 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___207_1056  ->
    match uu___207_1056 with
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
        let uu____1058 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1058
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1061 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1061
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1072 =
          let uu____1073 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1073 in
        let uu____1076 =
          let uu____1077 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1077 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1072 uu____1076
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1096 =
          let uu____1097 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1097 in
        let uu____1100 =
          let uu____1101 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1101 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1096 uu____1100
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1111 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1111
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
    | uu____1121 ->
        let uu____1124 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1124 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1141 ->
        let uu____1144 = quals_to_string quals in Prims.strcat uu____1144 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1200 =
      let uu____1201 = FStar_Options.ugly () in Prims.op_Negation uu____1201 in
    if uu____1200
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1207 = FStar_Options.print_implicits () in
         if uu____1207 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1209 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1234,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1270 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1300 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1318  ->
                                 match uu____1318 with
                                 | (t1,uu____1324) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1300
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1270 (FStar_String.concat "\\/") in
           let uu____1329 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1329
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1341 = tag_of_term t in
           let uu____1342 = sli m in
           let uu____1343 = term_to_string t' in
           let uu____1344 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1341 uu____1342
             uu____1343 uu____1344
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1357 = tag_of_term t in
           let uu____1358 = term_to_string t' in
           let uu____1359 = sli m0 in
           let uu____1360 = sli m1 in
           let uu____1361 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1357
             uu____1358 uu____1359 uu____1360 uu____1361
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1363,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1377 = FStar_Range.string_of_range r in
           let uu____1378 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1377
             uu____1378
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1380) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1386 = db_to_string x3 in
           let uu____1387 =
             let uu____1388 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1388 in
           Prims.strcat uu____1386 uu____1387
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1392) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1419 = FStar_Options.print_universes () in
           if uu____1419
           then
             let uu____1420 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1420
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1440 = binders_to_string " -> " bs in
           let uu____1441 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1440 uu____1441
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1466 = binders_to_string " " bs in
                let uu____1467 = term_to_string t2 in
                let uu____1468 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1472 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1472) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1466 uu____1467
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1468
            | uu____1475 ->
                let uu____1478 = binders_to_string " " bs in
                let uu____1479 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1478 uu____1479)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1486 = bv_to_string xt in
           let uu____1487 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1490 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1486 uu____1487 uu____1490
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1515 = term_to_string t in
           let uu____1516 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1515 uu____1516
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1535 = lbs_to_string [] lbs in
           let uu____1536 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1535 uu____1536
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1597 =
                   let uu____1598 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1598
                     (FStar_Util.dflt "default") in
                 let uu____1603 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1597 uu____1603
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1619 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1619 in
           let uu____1620 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1620 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1659 = term_to_string head1 in
           let uu____1660 =
             let uu____1661 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1697  ->
                       match uu____1697 with
                       | (p,wopt,e) ->
                           let uu____1713 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1714 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1716 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1716 in
                           let uu____1717 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1713
                             uu____1714 uu____1717)) in
             FStar_Util.concat_l "\n\t|" uu____1661 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1659 uu____1660
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1724 = FStar_Options.print_universes () in
           if uu____1724
           then
             let uu____1725 = term_to_string t in
             let uu____1726 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1725 uu____1726
           else term_to_string t
       | uu____1728 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1730 =
      let uu____1731 = FStar_Options.ugly () in Prims.op_Negation uu____1731 in
    if uu____1730
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1753 = fv_to_string l in
           let uu____1754 =
             let uu____1755 =
               FStar_List.map
                 (fun uu____1766  ->
                    match uu____1766 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1755 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1753 uu____1754
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1778) ->
           let uu____1783 = FStar_Options.print_bound_var_types () in
           if uu____1783
           then
             let uu____1784 = bv_to_string x1 in
             let uu____1785 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1784 uu____1785
           else
             (let uu____1787 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1787)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1789 = FStar_Options.print_bound_var_types () in
           if uu____1789
           then
             let uu____1790 = bv_to_string x1 in
             let uu____1791 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1790 uu____1791
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1795 = FStar_Options.print_real_names () in
           if uu____1795
           then
             let uu____1796 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1796
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1815 = FStar_Options.print_universes () in
        if uu____1815
        then
          let uu____1822 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1840 =
                      let uu____1845 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1845 in
                    match uu____1840 with
                    | (us,td) ->
                        let uu____1848 =
                          let uu____1857 =
                            let uu____1858 = FStar_Syntax_Subst.compress td in
                            uu____1858.FStar_Syntax_Syntax.n in
                          match uu____1857 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1869,(t,uu____1871)::(d,uu____1873)::[])
                              -> (t, d)
                          | uu____1916 -> failwith "Impossibe" in
                        (match uu____1848 with
                         | (t,d) ->
                             let uu___214_1935 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___214_1935.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___214_1935.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1822)
        else lbs in
      let uu____1941 = quals_to_string' quals in
      let uu____1942 =
        let uu____1943 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1958 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1959 =
                    let uu____1960 = FStar_Options.print_universes () in
                    if uu____1960
                    then
                      let uu____1961 =
                        let uu____1962 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1962 ">" in
                      Prims.strcat "<" uu____1961
                    else "" in
                  let uu____1964 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1965 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1958 uu____1959
                    uu____1964 uu____1965)) in
        FStar_Util.concat_l "\n and " uu____1943 in
      FStar_Util.format3 "%slet %s %s" uu____1941
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1942
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1972 = FStar_Options.print_effect_args () in
    if uu____1972
    then
      let uu____1973 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1973
    else
      (let uu____1975 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1976 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1975 uu____1976)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___208_1978  ->
      match uu___208_1978 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1981 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1986 =
        let uu____1987 = FStar_Options.ugly () in
        Prims.op_Negation uu____1987 in
      if uu____1986
      then
        let uu____1988 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1988 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1994 = b in
         match uu____1994 with
         | (a,imp) ->
             let uu____1997 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1997
             then
               let uu____1998 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1998
             else
               (let uu____2000 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2002 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____2002) in
                if uu____2000
                then
                  let uu____2003 = nm_to_string a in
                  imp_to_string uu____2003 imp
                else
                  (let uu____2005 =
                     let uu____2006 = nm_to_string a in
                     let uu____2007 =
                       let uu____2008 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____2008 in
                     Prims.strcat uu____2006 uu____2007 in
                   imp_to_string uu____2005 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2014 = FStar_Options.print_implicits () in
        if uu____2014 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____2016 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____2016 (FStar_String.concat sep)
      else
        (let uu____2024 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____2024 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___209_2031  ->
    match uu___209_2031 with
    | (a,imp) ->
        let uu____2044 = term_to_string a in imp_to_string uu____2044 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____2047 = FStar_Options.print_implicits () in
      if uu____2047 then args else filter_imp args in
    let uu____2051 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2051 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____2065 =
      let uu____2066 = FStar_Options.ugly () in Prims.op_Negation uu____2066 in
    if uu____2065
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2080 =
             let uu____2081 = FStar_Syntax_Subst.compress t in
             uu____2081.FStar_Syntax_Syntax.n in
           (match uu____2080 with
            | FStar_Syntax_Syntax.Tm_type uu____2084 when
                let uu____2085 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2085 -> term_to_string t
            | uu____2086 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2088 = univ_to_string u in
                     let uu____2089 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2088 uu____2089
                 | uu____2090 ->
                     let uu____2093 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2093))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2104 =
             let uu____2105 = FStar_Syntax_Subst.compress t in
             uu____2105.FStar_Syntax_Syntax.n in
           (match uu____2104 with
            | FStar_Syntax_Syntax.Tm_type uu____2108 when
                let uu____2109 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2109 -> term_to_string t
            | uu____2110 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2112 = univ_to_string u in
                     let uu____2113 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2112 uu____2113
                 | uu____2114 ->
                     let uu____2117 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2117))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2120 = FStar_Options.print_effect_args () in
             if uu____2120
             then
               let uu____2121 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2122 =
                 let uu____2123 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2123 (FStar_String.concat ", ") in
               let uu____2130 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2131 =
                 let uu____2132 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2132 (FStar_String.concat ", ") in
               let uu____2153 =
                 let uu____2154 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2154 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2121
                 uu____2122 uu____2130 uu____2131 uu____2153
             else
               (let uu____2164 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_2168  ->
                           match uu___210_2168 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2169 -> false)))
                    &&
                    (let uu____2171 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2171) in
                if uu____2164
                then
                  let uu____2172 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2172
                else
                  (let uu____2174 =
                     ((let uu____2177 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2177) &&
                        (let uu____2179 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2179))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2174
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2181 =
                        (let uu____2184 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2184) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2188  ->
                                   match uu___211_2188 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2189 -> false))) in
                      if uu____2181
                      then
                        let uu____2190 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2190
                      else
                        (let uu____2192 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2193 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2192 uu____2193)))) in
           let dec =
             let uu____2195 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2205  ->
                       match uu___212_2205 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2211 =
                             let uu____2212 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2212 in
                           [uu____2211]
                       | uu____2213 -> [])) in
             FStar_All.pipe_right uu____2195 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2217 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2227 = b in
    match uu____2227 with
    | (a,imp) ->
        let n1 =
          let uu____2231 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2231
          then FStar_Util.JsonNull
          else
            (let uu____2233 =
               let uu____2234 = nm_to_string a in
               imp_to_string uu____2234 imp in
             FStar_Util.JsonStr uu____2233) in
        let t =
          let uu____2236 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2236 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2253 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2253
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2260 = FStar_Options.print_universes () in
    if uu____2260 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2266 =
      let uu____2267 = FStar_Options.ugly () in Prims.op_Negation uu____2267 in
    if uu____2266
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2271 = s in
       match uu____2271 with
       | (us,t) ->
           let uu____2278 =
             let uu____2279 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2279 in
           let uu____2280 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2278 uu____2280)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2285 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2286 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2287 =
      let uu____2288 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2288 in
    let uu____2289 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2290 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2285 uu____2286 uu____2287
      uu____2289 uu____2290
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
          let uu____2311 =
            let uu____2312 = FStar_Options.ugly () in
            Prims.op_Negation uu____2312 in
          if uu____2311
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2324 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2324 (FStar_String.concat ",\n\t") in
             let uu____2333 =
               let uu____2336 =
                 let uu____2339 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2340 =
                   let uu____2343 =
                     let uu____2344 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2344 in
                   let uu____2345 =
                     let uu____2348 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2349 =
                       let uu____2352 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2353 =
                         let uu____2356 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2357 =
                           let uu____2360 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2361 =
                             let uu____2364 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2365 =
                               let uu____2368 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2369 =
                                 let uu____2372 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2373 =
                                   let uu____2376 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2377 =
                                     let uu____2380 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2381 =
                                       let uu____2384 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2385 =
                                         let uu____2388 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2389 =
                                           let uu____2392 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2393 =
                                             let uu____2396 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2397 =
                                               let uu____2400 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2401 =
                                                 let uu____2404 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2405 =
                                                   let uu____2408 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2408] in
                                                 uu____2404 :: uu____2405 in
                                               uu____2400 :: uu____2401 in
                                             uu____2396 :: uu____2397 in
                                           uu____2392 :: uu____2393 in
                                         uu____2388 :: uu____2389 in
                                       uu____2384 :: uu____2385 in
                                     uu____2380 :: uu____2381 in
                                   uu____2376 :: uu____2377 in
                                 uu____2372 :: uu____2373 in
                               uu____2368 :: uu____2369 in
                             uu____2364 :: uu____2365 in
                           uu____2360 :: uu____2361 in
                         uu____2356 :: uu____2357 in
                       uu____2352 :: uu____2353 in
                     uu____2348 :: uu____2349 in
                   uu____2343 :: uu____2345 in
                 uu____2339 :: uu____2340 in
               (if for_free then "_for_free " else "") :: uu____2336 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2333)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2422 =
      let uu____2423 = FStar_Options.ugly () in Prims.op_Negation uu____2423 in
    if uu____2422
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2429 -> ""
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
           (lid,univs1,tps,k,uu____2439,uu____2440) ->
           let uu____2449 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2450 = binders_to_string " " tps in
           let uu____2451 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2449
             lid.FStar_Ident.str uu____2450 uu____2451
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2455,uu____2456,uu____2457) ->
           let uu____2462 = FStar_Options.print_universes () in
           if uu____2462
           then
             let uu____2463 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2463 with
              | (univs2,t1) ->
                  let uu____2470 = univ_names_to_string univs2 in
                  let uu____2471 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2470
                    lid.FStar_Ident.str uu____2471)
           else
             (let uu____2473 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2473)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2477 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2477 with
            | (univs2,t1) ->
                let uu____2484 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2485 =
                  let uu____2486 = FStar_Options.print_universes () in
                  if uu____2486
                  then
                    let uu____2487 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2487
                  else "" in
                let uu____2489 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2484
                  lid.FStar_Ident.str uu____2485 uu____2489)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2491,f) ->
           let uu____2493 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2493
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2495) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2501 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2501
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2503) ->
           let uu____2512 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2512 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2530) -> lift_wp
             | (uu____2537,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2545 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2545 with
            | (us,t) ->
                let uu____2556 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2557 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2558 = univ_names_to_string us in
                let uu____2559 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2556
                  uu____2557 uu____2558 uu____2559)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2569 = FStar_Options.print_universes () in
           if uu____2569
           then
             let uu____2570 =
               let uu____2575 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2575 in
             (match uu____2570 with
              | (univs2,t) ->
                  let uu____2578 =
                    let uu____2591 =
                      let uu____2592 = FStar_Syntax_Subst.compress t in
                      uu____2592.FStar_Syntax_Syntax.n in
                    match uu____2591 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2633 -> failwith "impossible" in
                  (match uu____2578 with
                   | (tps1,c1) ->
                       let uu____2664 = sli l in
                       let uu____2665 = univ_names_to_string univs2 in
                       let uu____2666 = binders_to_string " " tps1 in
                       let uu____2667 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2664
                         uu____2665 uu____2666 uu____2667))
           else
             (let uu____2669 = sli l in
              let uu____2670 = binders_to_string " " tps in
              let uu____2671 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2669 uu____2670
                uu____2671))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2680 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2680 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2685,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2687;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2689;
                       FStar_Syntax_Syntax.lbdef = uu____2690;_}::[]),uu____2691)
        ->
        let uu____2714 = lbname_to_string lb in
        let uu____2715 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2714 uu____2715
    | uu____2716 ->
        let uu____2717 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2717 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2732 = sli m.FStar_Syntax_Syntax.name in
    let uu____2733 =
      let uu____2734 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2734 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2732 uu____2733
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___213_2742  ->
    match uu___213_2742 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2745 = FStar_Util.string_of_int i in
        let uu____2746 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2745 uu____2746
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2749 = bv_to_string x in
        let uu____2750 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2749 uu____2750
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2757 = bv_to_string x in
        let uu____2758 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2757 uu____2758
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2761 = FStar_Util.string_of_int i in
        let uu____2762 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2761 uu____2762
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2765 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2765
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2770 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2770 (FStar_String.concat "; ")
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
           (let uu____2842 = f x in
            FStar_Util.string_builder_append strb uu____2842);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2849 = f x1 in
                 FStar_Util.string_builder_append strb uu____2849)) xs;
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
           (let uu____2885 = f x in
            FStar_Util.string_builder_append strb uu____2885);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2892 = f x1 in
                 FStar_Util.string_builder_append strb uu____2892)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)