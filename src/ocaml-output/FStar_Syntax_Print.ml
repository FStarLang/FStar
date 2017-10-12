open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___201_4  ->
    match uu___201_4 with
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
  fun uu___202_261  ->
    match uu___202_261 with
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
         (fun uu___203_326  ->
            match uu___203_326 with
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
  fun uu___204_638  ->
    match uu___204_638 with
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
  fun uu___205_1056  ->
    match uu___205_1056 with
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
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1363,s,uu____1365)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1382 = FStar_Range.string_of_range r in
           let uu____1383 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1382
             uu____1383
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1385) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1391 = db_to_string x3 in
           let uu____1392 =
             let uu____1393 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1393 in
           Prims.strcat uu____1391 uu____1392
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1397) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1424 = FStar_Options.print_universes () in
           if uu____1424
           then
             let uu____1425 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1425
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1445 = binders_to_string " -> " bs in
           let uu____1446 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1445 uu____1446
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1471 = binders_to_string " " bs in
                let uu____1472 = term_to_string t2 in
                let uu____1473 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1477 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1477) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1471 uu____1472
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1473
            | uu____1480 ->
                let uu____1483 = binders_to_string " " bs in
                let uu____1484 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1483 uu____1484)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1491 = bv_to_string xt in
           let uu____1492 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1495 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1491 uu____1492 uu____1495
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1520 = term_to_string t in
           let uu____1521 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1520 uu____1521
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1540 = lbs_to_string [] lbs in
           let uu____1541 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1540 uu____1541
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1602 =
                   let uu____1603 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1603
                     (FStar_Util.dflt "default") in
                 let uu____1608 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1602 uu____1608
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1624 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1624 in
           let uu____1625 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1625 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1664 = term_to_string head1 in
           let uu____1665 =
             let uu____1666 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1702  ->
                       match uu____1702 with
                       | (p,wopt,e) ->
                           let uu____1718 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1719 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1721 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1721 in
                           let uu____1722 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1718
                             uu____1719 uu____1722)) in
             FStar_Util.concat_l "\n\t|" uu____1666 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1664 uu____1665
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1729 = FStar_Options.print_universes () in
           if uu____1729
           then
             let uu____1730 = term_to_string t in
             let uu____1731 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1730 uu____1731
           else term_to_string t
       | uu____1733 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1735 =
      let uu____1736 = FStar_Options.ugly () in Prims.op_Negation uu____1736 in
    if uu____1735
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1758 = fv_to_string l in
           let uu____1759 =
             let uu____1760 =
               FStar_List.map
                 (fun uu____1771  ->
                    match uu____1771 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1760 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1758 uu____1759
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1783) ->
           let uu____1788 = FStar_Options.print_bound_var_types () in
           if uu____1788
           then
             let uu____1789 = bv_to_string x1 in
             let uu____1790 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1789 uu____1790
           else
             (let uu____1792 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1792)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1794 = FStar_Options.print_bound_var_types () in
           if uu____1794
           then
             let uu____1795 = bv_to_string x1 in
             let uu____1796 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1795 uu____1796
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1800 = FStar_Options.print_real_names () in
           if uu____1800
           then
             let uu____1801 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1801
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1820 = FStar_Options.print_universes () in
        if uu____1820
        then
          let uu____1827 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1845 =
                      let uu____1850 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1850 in
                    match uu____1845 with
                    | (us,td) ->
                        let uu____1853 =
                          let uu____1862 =
                            let uu____1863 = FStar_Syntax_Subst.compress td in
                            uu____1863.FStar_Syntax_Syntax.n in
                          match uu____1862 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1874,(t,uu____1876)::(d,uu____1878)::[])
                              -> (t, d)
                          | uu____1921 -> failwith "Impossibe" in
                        (match uu____1853 with
                         | (t,d) ->
                             let uu___212_1940 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___212_1940.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___212_1940.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1827)
        else lbs in
      let uu____1946 = quals_to_string' quals in
      let uu____1947 =
        let uu____1948 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1963 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1964 =
                    let uu____1965 = FStar_Options.print_universes () in
                    if uu____1965
                    then
                      let uu____1966 =
                        let uu____1967 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1967 ">" in
                      Prims.strcat "<" uu____1966
                    else "" in
                  let uu____1969 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1970 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1963 uu____1964
                    uu____1969 uu____1970)) in
        FStar_Util.concat_l "\n and " uu____1948 in
      FStar_Util.format3 "%slet %s %s" uu____1946
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1947
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1977 = FStar_Options.print_effect_args () in
    if uu____1977
    then
      let uu____1978 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1978
    else
      (let uu____1980 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1981 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1980 uu____1981)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___206_1983  ->
      match uu___206_1983 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1986 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1991 =
        let uu____1992 = FStar_Options.ugly () in
        Prims.op_Negation uu____1992 in
      if uu____1991
      then
        let uu____1993 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1993 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1999 = b in
         match uu____1999 with
         | (a,imp) ->
             let uu____2002 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____2002
             then
               let uu____2003 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____2003
             else
               (let uu____2005 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2007 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____2007) in
                if uu____2005
                then
                  let uu____2008 = nm_to_string a in
                  imp_to_string uu____2008 imp
                else
                  (let uu____2010 =
                     let uu____2011 = nm_to_string a in
                     let uu____2012 =
                       let uu____2013 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____2013 in
                     Prims.strcat uu____2011 uu____2012 in
                   imp_to_string uu____2010 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2019 = FStar_Options.print_implicits () in
        if uu____2019 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____2021 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____2021 (FStar_String.concat sep)
      else
        (let uu____2029 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____2029 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___207_2036  ->
    match uu___207_2036 with
    | (a,imp) ->
        let uu____2049 = term_to_string a in imp_to_string uu____2049 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____2052 = FStar_Options.print_implicits () in
      if uu____2052 then args else filter_imp args in
    let uu____2056 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2056 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____2070 =
      let uu____2071 = FStar_Options.ugly () in Prims.op_Negation uu____2071 in
    if uu____2070
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2085 =
             let uu____2086 = FStar_Syntax_Subst.compress t in
             uu____2086.FStar_Syntax_Syntax.n in
           (match uu____2085 with
            | FStar_Syntax_Syntax.Tm_type uu____2089 when
                let uu____2090 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2090 -> term_to_string t
            | uu____2091 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2093 = univ_to_string u in
                     let uu____2094 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2093 uu____2094
                 | uu____2095 ->
                     let uu____2098 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2098))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2109 =
             let uu____2110 = FStar_Syntax_Subst.compress t in
             uu____2110.FStar_Syntax_Syntax.n in
           (match uu____2109 with
            | FStar_Syntax_Syntax.Tm_type uu____2113 when
                let uu____2114 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2114 -> term_to_string t
            | uu____2115 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2117 = univ_to_string u in
                     let uu____2118 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2117 uu____2118
                 | uu____2119 ->
                     let uu____2122 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2122))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2125 = FStar_Options.print_effect_args () in
             if uu____2125
             then
               let uu____2126 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2127 =
                 let uu____2128 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2128 (FStar_String.concat ", ") in
               let uu____2135 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2136 =
                 let uu____2137 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2137 (FStar_String.concat ", ") in
               let uu____2158 =
                 let uu____2159 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2159 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2126
                 uu____2127 uu____2135 uu____2136 uu____2158
             else
               (let uu____2169 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___208_2173  ->
                           match uu___208_2173 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2174 -> false)))
                    &&
                    (let uu____2176 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2176) in
                if uu____2169
                then
                  let uu____2177 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2177
                else
                  (let uu____2179 =
                     ((let uu____2182 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2182) &&
                        (let uu____2184 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2184))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2179
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2186 =
                        (let uu____2189 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2189) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___209_2193  ->
                                   match uu___209_2193 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2194 -> false))) in
                      if uu____2186
                      then
                        let uu____2195 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2195
                      else
                        (let uu____2197 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2198 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2197 uu____2198)))) in
           let dec =
             let uu____2200 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___210_2210  ->
                       match uu___210_2210 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2216 =
                             let uu____2217 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2217 in
                           [uu____2216]
                       | uu____2218 -> [])) in
             FStar_All.pipe_right uu____2200 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2222 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2232 = b in
    match uu____2232 with
    | (a,imp) ->
        let n1 =
          let uu____2236 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2236
          then FStar_Util.JsonNull
          else
            (let uu____2238 =
               let uu____2239 = nm_to_string a in
               imp_to_string uu____2239 imp in
             FStar_Util.JsonStr uu____2238) in
        let t =
          let uu____2241 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2241 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2258 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2258
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2265 = FStar_Options.print_universes () in
    if uu____2265 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2271 =
      let uu____2272 = FStar_Options.ugly () in Prims.op_Negation uu____2272 in
    if uu____2271
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2276 = s in
       match uu____2276 with
       | (us,t) ->
           let uu____2283 =
             let uu____2284 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2284 in
           let uu____2285 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2283 uu____2285)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2290 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2291 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2292 =
      let uu____2293 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2293 in
    let uu____2294 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2295 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2290 uu____2291 uu____2292
      uu____2294 uu____2295
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
          let uu____2316 =
            let uu____2317 = FStar_Options.ugly () in
            Prims.op_Negation uu____2317 in
          if uu____2316
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2329 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2329 (FStar_String.concat ",\n\t") in
             let uu____2338 =
               let uu____2341 =
                 let uu____2344 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2345 =
                   let uu____2348 =
                     let uu____2349 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2349 in
                   let uu____2350 =
                     let uu____2353 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2354 =
                       let uu____2357 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2358 =
                         let uu____2361 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2362 =
                           let uu____2365 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2366 =
                             let uu____2369 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2370 =
                               let uu____2373 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2374 =
                                 let uu____2377 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2378 =
                                   let uu____2381 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2382 =
                                     let uu____2385 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2386 =
                                       let uu____2389 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2390 =
                                         let uu____2393 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2394 =
                                           let uu____2397 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2398 =
                                             let uu____2401 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2402 =
                                               let uu____2405 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2406 =
                                                 let uu____2409 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2410 =
                                                   let uu____2413 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2413] in
                                                 uu____2409 :: uu____2410 in
                                               uu____2405 :: uu____2406 in
                                             uu____2401 :: uu____2402 in
                                           uu____2397 :: uu____2398 in
                                         uu____2393 :: uu____2394 in
                                       uu____2389 :: uu____2390 in
                                     uu____2385 :: uu____2386 in
                                   uu____2381 :: uu____2382 in
                                 uu____2377 :: uu____2378 in
                               uu____2373 :: uu____2374 in
                             uu____2369 :: uu____2370 in
                           uu____2365 :: uu____2366 in
                         uu____2361 :: uu____2362 in
                       uu____2357 :: uu____2358 in
                     uu____2353 :: uu____2354 in
                   uu____2348 :: uu____2350 in
                 uu____2344 :: uu____2345 in
               (if for_free then "_for_free " else "") :: uu____2341 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2338)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2427 =
      let uu____2428 = FStar_Options.ugly () in Prims.op_Negation uu____2428 in
    if uu____2427
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2434 -> ""
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
           (lid,univs1,tps,k,uu____2444,uu____2445) ->
           let uu____2454 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2455 = binders_to_string " " tps in
           let uu____2456 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2454
             lid.FStar_Ident.str uu____2455 uu____2456
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2460,uu____2461,uu____2462) ->
           let uu____2467 = FStar_Options.print_universes () in
           if uu____2467
           then
             let uu____2468 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2468 with
              | (univs2,t1) ->
                  let uu____2475 = univ_names_to_string univs2 in
                  let uu____2476 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2475
                    lid.FStar_Ident.str uu____2476)
           else
             (let uu____2478 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2478)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2482 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2482 with
            | (univs2,t1) ->
                let uu____2489 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2490 =
                  let uu____2491 = FStar_Options.print_universes () in
                  if uu____2491
                  then
                    let uu____2492 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2492
                  else "" in
                let uu____2494 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2489
                  lid.FStar_Ident.str uu____2490 uu____2494)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2496,f) ->
           let uu____2498 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2498
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2500) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2506 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2506
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2508) ->
           let uu____2517 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2517 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2535) -> lift_wp
             | (uu____2542,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2550 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2550 with
            | (us,t) ->
                let uu____2561 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2562 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2563 = univ_names_to_string us in
                let uu____2564 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2561
                  uu____2562 uu____2563 uu____2564)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2574 = FStar_Options.print_universes () in
           if uu____2574
           then
             let uu____2575 =
               let uu____2580 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2580 in
             (match uu____2575 with
              | (univs2,t) ->
                  let uu____2583 =
                    let uu____2596 =
                      let uu____2597 = FStar_Syntax_Subst.compress t in
                      uu____2597.FStar_Syntax_Syntax.n in
                    match uu____2596 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2638 -> failwith "impossible" in
                  (match uu____2583 with
                   | (tps1,c1) ->
                       let uu____2669 = sli l in
                       let uu____2670 = univ_names_to_string univs2 in
                       let uu____2671 = binders_to_string " " tps1 in
                       let uu____2672 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2669
                         uu____2670 uu____2671 uu____2672))
           else
             (let uu____2674 = sli l in
              let uu____2675 = binders_to_string " " tps in
              let uu____2676 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2674 uu____2675
                uu____2676))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2685 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2685 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2690,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2692;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2694;
                       FStar_Syntax_Syntax.lbdef = uu____2695;_}::[]),uu____2696)
        ->
        let uu____2719 = lbname_to_string lb in
        let uu____2720 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2719 uu____2720
    | uu____2721 ->
        let uu____2722 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2722 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2737 = sli m.FStar_Syntax_Syntax.name in
    let uu____2738 =
      let uu____2739 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2739 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2737 uu____2738
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___211_2747  ->
    match uu___211_2747 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2750 = FStar_Util.string_of_int i in
        let uu____2751 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2750 uu____2751
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2754 = bv_to_string x in
        let uu____2755 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2754 uu____2755
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2762 = bv_to_string x in
        let uu____2763 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2762 uu____2763
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2766 = FStar_Util.string_of_int i in
        let uu____2767 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2766 uu____2767
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2770 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2770
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2775 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2775 (FStar_String.concat "; ")
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
           (let uu____2847 = f x in
            FStar_Util.string_builder_append strb uu____2847);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2854 = f x1 in
                 FStar_Util.string_builder_append strb uu____2854)) xs;
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
           (let uu____2890 = f x in
            FStar_Util.string_builder_append strb uu____2890);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2897 = f x1 in
                 FStar_Util.string_builder_append strb uu____2897)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)