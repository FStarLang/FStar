open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___204_4  ->
    match uu___204_4 with
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
let is_prim_op ps f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_All.pipe_right ps
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
  | uu____188 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____207 -> failwith "get_lid"
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
let is_inr uu___205_281 =
  match uu___205_281 with
  | FStar_Util.Inl uu____286 -> false
  | FStar_Util.Inr uu____287 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___206_346  ->
          match uu___206_346 with
          | (uu____353,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____354)) -> false
          | uu____357 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____376 =
      let uu____377 = FStar_Syntax_Subst.compress e in
      uu____377.FStar_Syntax_Syntax.n in
    match uu____376 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____464 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____464
        then
          let uu____477 =
            let uu____486 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____486 in
          (match uu____477 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____512 =
                 let uu____519 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____519 :: xs in
               FStar_Pervasives_Native.Some uu____512
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____557 ->
        let uu____558 = is_lex_top e in
        if uu____558
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____612 = f hd1 in if uu____612 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____634 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____634
let infix_prim_op_to_string e =
  let uu____666 = get_lid e in find_lid uu____666 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____684 = get_lid e in find_lid uu____684 unary_prim_ops
let quant_to_string t =
  let uu____702 = get_lid t in find_lid uu____702 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____711) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____716 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____724) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____740 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____740
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___207_744  ->
    match uu___207_744 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____752 = db_to_string x in Prims.strcat "Tm_bvar: " uu____752
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____754 = nm_to_string x in Prims.strcat "Tm_name: " uu____754
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____756 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____756
    | FStar_Syntax_Syntax.Tm_uinst uu____757 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____766 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____767 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____768 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____787 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____802 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____811 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____830 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____859 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____894 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____909 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____930,m) ->
        let uu____980 = FStar_ST.read m in
        (match uu____980 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____999 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____1008 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____1021 = FStar_Options.hide_uvar_nums () in
    if uu____1021
    then "?"
    else
      (let uu____1023 =
         let uu____1024 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____1024 FStar_Util.string_of_int in
       Prims.strcat "?" uu____1023)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____1029 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____1030 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____1029 uu____1030
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____1035 = FStar_Options.hide_uvar_nums () in
    if uu____1035
    then "?"
    else
      (let uu____1037 =
         let uu____1038 =
           let uu____1039 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____1039 FStar_Util.string_of_int in
         let uu____1040 =
           let uu____1041 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____1041 in
         Prims.strcat uu____1038 uu____1040 in
       Prims.strcat "?" uu____1037)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____1060 = FStar_Syntax_Subst.compress_univ u in
      match uu____1060 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____1070 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____1077 =
      let uu____1078 = FStar_Options.ugly () in Prims.op_Negation uu____1078 in
    if uu____1077
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____1082 = FStar_Syntax_Subst.compress_univ u in
       match uu____1082 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____1094 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____1094
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____1096 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____1096 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____1110 = univ_to_string u2 in
                let uu____1111 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____1110 uu____1111)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____1115 =
             let uu____1116 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____1116 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____1115
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____1129 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____1129 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____1142 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1142 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___208_1152  ->
    match uu___208_1152 with
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
        let uu____1154 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1154
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1157 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1157
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1168 =
          let uu____1169 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1169 in
        let uu____1172 =
          let uu____1173 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1173 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1168 uu____1172
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1192 =
          let uu____1193 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1193 in
        let uu____1196 =
          let uu____1197 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1197 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1192 uu____1196
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1207 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1207
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
    | uu____1217 ->
        let uu____1220 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1220 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1237 ->
        let uu____1240 = quals_to_string quals in Prims.strcat uu____1240 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1298 =
      let uu____1299 = FStar_Options.ugly () in Prims.op_Negation uu____1299 in
    if uu____1298
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1305 = FStar_Options.print_implicits () in
         if uu____1305 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1307 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1336,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1386 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1418 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1436  ->
                                 match uu____1436 with
                                 | (t1,uu____1442) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1418
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1386 (FStar_String.concat "\\/") in
           let uu____1447 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1447
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1467 = tag_of_term t in
           let uu____1468 = sli m in
           let uu____1469 = term_to_string t' in
           let uu____1470 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1467 uu____1468
             uu____1469 uu____1470
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1491 = tag_of_term t in
           let uu____1492 = term_to_string t' in
           let uu____1493 = sli m0 in
           let uu____1494 = sli m1 in
           let uu____1495 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1491
             uu____1492 uu____1493 uu____1494 uu____1495
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1497,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1519 = FStar_Range.string_of_range r in
           let uu____1520 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1519
             uu____1520
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1522) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1532 = db_to_string x3 in
           let uu____1533 =
             let uu____1534 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1534 in
           Prims.strcat uu____1532 uu____1533
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1538) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1573 = FStar_Options.print_universes () in
           if uu____1573
           then
             let uu____1574 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1574
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1598 = binders_to_string " -> " bs in
           let uu____1599 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1598 uu____1599
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1628 = binders_to_string " " bs in
                let uu____1629 = term_to_string t2 in
                let uu____1630 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1636 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1636) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1628 uu____1629
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1630
            | uu____1641 ->
                let uu____1644 = binders_to_string " " bs in
                let uu____1645 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1644 uu____1645)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1656 = bv_to_string xt in
           let uu____1657 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1662 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1656 uu____1657 uu____1662
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1697 = term_to_string t in
           let uu____1698 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1697 uu____1698
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1721 = lbs_to_string [] lbs in
           let uu____1722 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1721 uu____1722
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1811 =
                   let uu____1812 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1812
                     (FStar_Util.dflt "default") in
                 let uu____1817 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1811 uu____1817
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1845 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1845 in
           let uu____1846 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1846 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1897 = term_to_string head1 in
           let uu____1898 =
             let uu____1899 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1939  ->
                       match uu____1939 with
                       | (p,wopt,e) ->
                           let uu____1955 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1956 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1958 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1958 in
                           let uu____1959 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1955
                             uu____1956 uu____1959)) in
             FStar_Util.concat_l "\n\t|" uu____1899 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1897 uu____1898
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1970 = FStar_Options.print_universes () in
           if uu____1970
           then
             let uu____1971 = term_to_string t in
             let uu____1972 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1971 uu____1972
           else term_to_string t
       | uu____1974 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1976 =
      let uu____1977 = FStar_Options.ugly () in Prims.op_Negation uu____1977 in
    if uu____1976
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1999 = fv_to_string l in
           let uu____2000 =
             let uu____2001 =
               FStar_List.map
                 (fun uu____2012  ->
                    match uu____2012 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____2001 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1999 uu____2000
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2024) ->
           let uu____2033 = FStar_Options.print_bound_var_types () in
           if uu____2033
           then
             let uu____2034 = bv_to_string x1 in
             let uu____2035 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____2034 uu____2035
           else
             (let uu____2037 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____2037)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2039 = FStar_Options.print_bound_var_types () in
           if uu____2039
           then
             let uu____2040 = bv_to_string x1 in
             let uu____2041 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____2040 uu____2041
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2045 = FStar_Options.print_real_names () in
           if uu____2045
           then
             let uu____2046 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____2046
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____2065 = FStar_Options.print_universes () in
        if uu____2065
        then
          let uu____2072 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____2090 =
                      let uu____2095 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____2095 in
                    match uu____2090 with
                    | (us,td) ->
                        let uu____2098 =
                          let uu____2111 =
                            let uu____2112 = FStar_Syntax_Subst.compress td in
                            uu____2112.FStar_Syntax_Syntax.n in
                          match uu____2111 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____2129,(t,uu____2131)::(d,uu____2133)::[])
                              -> (t, d)
                          | uu____2200 -> failwith "Impossibe" in
                        (match uu____2098 with
                         | (t,d) ->
                             let uu___215_2231 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___215_2231.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___215_2231.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____2072)
        else lbs in
      let uu____2237 = quals_to_string' quals in
      let uu____2238 =
        let uu____2239 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____2254 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____2255 =
                    let uu____2256 = FStar_Options.print_universes () in
                    if uu____2256
                    then
                      let uu____2257 =
                        let uu____2258 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____2258 ">" in
                      Prims.strcat "<" uu____2257
                    else "" in
                  let uu____2260 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____2261 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____2254 uu____2255
                    uu____2260 uu____2261)) in
        FStar_Util.concat_l "\n and " uu____2239 in
      FStar_Util.format3 "%slet %s %s" uu____2237
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____2238
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____2270 = FStar_Options.print_effect_args () in
    if uu____2270
    then
      let uu____2271 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____2271
    else
      (let uu____2273 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____2274 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____2273 uu____2274)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___209_2276  ->
      match uu___209_2276 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____2279 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____2284 =
        let uu____2285 = FStar_Options.ugly () in
        Prims.op_Negation uu____2285 in
      if uu____2284
      then
        let uu____2286 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____2286 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2292 = b in
         match uu____2292 with
         | (a,imp) ->
             let uu____2295 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____2295
             then
               let uu____2296 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____2296
             else
               (let uu____2298 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2300 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____2300) in
                if uu____2298
                then
                  let uu____2301 = nm_to_string a in
                  imp_to_string uu____2301 imp
                else
                  (let uu____2303 =
                     let uu____2304 = nm_to_string a in
                     let uu____2305 =
                       let uu____2306 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____2306 in
                     Prims.strcat uu____2304 uu____2305 in
                   imp_to_string uu____2303 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2312 = FStar_Options.print_implicits () in
        if uu____2312 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____2314 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____2314 (FStar_String.concat sep)
      else
        (let uu____2322 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____2322 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___210_2329  ->
    match uu___210_2329 with
    | (a,imp) ->
        let uu____2342 = term_to_string a in imp_to_string uu____2342 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____2345 = FStar_Options.print_implicits () in
      if uu____2345 then args else filter_imp args in
    let uu____2351 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2351 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____2365 =
      let uu____2366 = FStar_Options.ugly () in Prims.op_Negation uu____2366 in
    if uu____2365
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2384 =
             let uu____2385 = FStar_Syntax_Subst.compress t in
             uu____2385.FStar_Syntax_Syntax.n in
           (match uu____2384 with
            | FStar_Syntax_Syntax.Tm_type uu____2390 when
                let uu____2391 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2391 -> term_to_string t
            | uu____2392 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2394 = univ_to_string u in
                     let uu____2395 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2394 uu____2395
                 | uu____2396 ->
                     let uu____2399 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2399))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2414 =
             let uu____2415 = FStar_Syntax_Subst.compress t in
             uu____2415.FStar_Syntax_Syntax.n in
           (match uu____2414 with
            | FStar_Syntax_Syntax.Tm_type uu____2420 when
                let uu____2421 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2421 -> term_to_string t
            | uu____2422 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2424 = univ_to_string u in
                     let uu____2425 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2424 uu____2425
                 | uu____2426 ->
                     let uu____2429 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2429))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2432 = FStar_Options.print_effect_args () in
             if uu____2432
             then
               let uu____2433 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2434 =
                 let uu____2435 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2435 (FStar_String.concat ", ") in
               let uu____2442 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2443 =
                 let uu____2444 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2444 (FStar_String.concat ", ") in
               let uu____2467 =
                 let uu____2468 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2468 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2433
                 uu____2434 uu____2442 uu____2443 uu____2467
             else
               (let uu____2478 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___211_2482  ->
                           match uu___211_2482 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2483 -> false)))
                    &&
                    (let uu____2485 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2485) in
                if uu____2478
                then
                  let uu____2486 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2486
                else
                  (let uu____2488 =
                     ((let uu____2491 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2491) &&
                        (let uu____2493 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2493))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2488
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2495 =
                        (let uu____2498 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2498) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___212_2502  ->
                                   match uu___212_2502 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2503 -> false))) in
                      if uu____2495
                      then
                        let uu____2504 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2504
                      else
                        (let uu____2506 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2507 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2506 uu____2507)))) in
           let dec =
             let uu____2509 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___213_2519  ->
                       match uu___213_2519 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2527 =
                             let uu____2528 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2528 in
                           [uu____2527]
                       | uu____2529 -> [])) in
             FStar_All.pipe_right uu____2509 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2533 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2547 = FStar_Options.print_universes () in
    if uu____2547 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2553 =
      let uu____2554 = FStar_Options.ugly () in Prims.op_Negation uu____2554 in
    if uu____2553
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2558 = s in
       match uu____2558 with
       | (us,t) ->
           let uu____2565 =
             let uu____2566 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2566 in
           let uu____2567 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2565 uu____2567)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2572 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2573 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2574 =
      let uu____2575 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2575 in
    let uu____2576 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2577 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2572 uu____2573 uu____2574
      uu____2576 uu____2577
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
          let uu____2598 =
            let uu____2599 = FStar_Options.ugly () in
            Prims.op_Negation uu____2599 in
          if uu____2598
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2611 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2611 (FStar_String.concat ",\n\t") in
             let uu____2620 =
               let uu____2623 =
                 let uu____2626 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2627 =
                   let uu____2630 =
                     let uu____2631 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2631 in
                   let uu____2632 =
                     let uu____2635 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2636 =
                       let uu____2639 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2640 =
                         let uu____2643 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2644 =
                           let uu____2647 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2648 =
                             let uu____2651 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2652 =
                               let uu____2655 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2656 =
                                 let uu____2659 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2660 =
                                   let uu____2663 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2664 =
                                     let uu____2667 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2668 =
                                       let uu____2671 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2672 =
                                         let uu____2675 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2676 =
                                           let uu____2679 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2680 =
                                             let uu____2683 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2684 =
                                               let uu____2687 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2688 =
                                                 let uu____2691 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2692 =
                                                   let uu____2695 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2695] in
                                                 uu____2691 :: uu____2692 in
                                               uu____2687 :: uu____2688 in
                                             uu____2683 :: uu____2684 in
                                           uu____2679 :: uu____2680 in
                                         uu____2675 :: uu____2676 in
                                       uu____2671 :: uu____2672 in
                                     uu____2667 :: uu____2668 in
                                   uu____2663 :: uu____2664 in
                                 uu____2659 :: uu____2660 in
                               uu____2655 :: uu____2656 in
                             uu____2651 :: uu____2652 in
                           uu____2647 :: uu____2648 in
                         uu____2643 :: uu____2644 in
                       uu____2639 :: uu____2640 in
                     uu____2635 :: uu____2636 in
                   uu____2630 :: uu____2632 in
                 uu____2626 :: uu____2627 in
               (if for_free then "_for_free " else "") :: uu____2623 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2620)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2709 =
      let uu____2710 = FStar_Options.ugly () in Prims.op_Negation uu____2710 in
    if uu____2709
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2716 -> ""
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
           (lid,univs1,tps,k,uu____2726,uu____2727) ->
           let uu____2736 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2737 = binders_to_string " " tps in
           let uu____2738 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2736
             lid.FStar_Ident.str uu____2737 uu____2738
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2742,uu____2743,uu____2744) ->
           let uu____2749 = FStar_Options.print_universes () in
           if uu____2749
           then
             let uu____2750 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2750 with
              | (univs2,t1) ->
                  let uu____2757 = univ_names_to_string univs2 in
                  let uu____2758 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2757
                    lid.FStar_Ident.str uu____2758)
           else
             (let uu____2760 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2760)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2764 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2764 with
            | (univs2,t1) ->
                let uu____2771 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2772 =
                  let uu____2773 = FStar_Options.print_universes () in
                  if uu____2773
                  then
                    let uu____2774 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2774
                  else "" in
                let uu____2776 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2771
                  lid.FStar_Ident.str uu____2772 uu____2776)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2778,f) ->
           let uu____2780 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2780
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2782) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2788 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2788
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2790) ->
           let uu____2799 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2799 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2817) -> lift_wp
             | (uu____2824,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2832 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2832 with
            | (us,t) ->
                let uu____2843 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2844 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2845 = univ_names_to_string us in
                let uu____2846 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2843
                  uu____2844 uu____2845 uu____2846)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2856 = FStar_Options.print_universes () in
           if uu____2856
           then
             let uu____2857 =
               let uu____2862 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2862 in
             (match uu____2857 with
              | (univs2,t) ->
                  let uu____2865 =
                    let uu____2880 =
                      let uu____2881 = FStar_Syntax_Subst.compress t in
                      uu____2881.FStar_Syntax_Syntax.n in
                    match uu____2880 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2932 -> failwith "impossible" in
                  (match uu____2865 with
                   | (tps1,c1) ->
                       let uu____2969 = sli l in
                       let uu____2970 = univ_names_to_string univs2 in
                       let uu____2971 = binders_to_string " " tps1 in
                       let uu____2972 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2969
                         uu____2970 uu____2971 uu____2972))
           else
             (let uu____2974 = sli l in
              let uu____2975 = binders_to_string " " tps in
              let uu____2976 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2974 uu____2975
                uu____2976))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2985 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2985 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2990,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2992;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2994;
                       FStar_Syntax_Syntax.lbdef = uu____2995;_}::[]),uu____2996)
        ->
        let uu____3023 = lbname_to_string lb in
        let uu____3024 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____3023 uu____3024
    | uu____3025 ->
        let uu____3026 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____3026 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____3041 = sli m.FStar_Syntax_Syntax.name in
    let uu____3042 =
      let uu____3043 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3043 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____3041 uu____3042
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___214_3051  ->
    match uu___214_3051 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____3054 = FStar_Util.string_of_int i in
        let uu____3055 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____3054 uu____3055
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____3058 = bv_to_string x in
        let uu____3059 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____3058 uu____3059
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____3070 = bv_to_string x in
        let uu____3071 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____3070 uu____3071
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____3074 = FStar_Util.string_of_int i in
        let uu____3075 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____3074 uu____3075
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____3078 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____3078
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____3083 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____3083 (FStar_String.concat "; ")
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
       (let uu____3155 = f x in
        FStar_Util.string_builder_append strb uu____3155);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____3162 = f x1 in
             FStar_Util.string_builder_append strb uu____3162)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____3198 = f x in
        FStar_Util.string_builder_append strb uu____3198);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____3205 = f x1 in
             FStar_Util.string_builder_append strb uu____3205)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)