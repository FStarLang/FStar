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
         | FStar_Pervasives_Native.Some uu____881 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____886 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____897 = FStar_Options.hide_uvar_nums () in
    if uu____897
    then "?"
    else
      (let uu____899 =
         let uu____900 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____900 FStar_Util.string_of_int in
       Prims.strcat "?" uu____899)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____905 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____906 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____905 uu____906
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____911 = FStar_Options.hide_uvar_nums () in
    if uu____911
    then "?"
    else
      (let uu____913 =
         let uu____914 =
           let uu____915 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____915 FStar_Util.string_of_int in
         let uu____916 =
           let uu____917 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____917 in
         Prims.strcat uu____914 uu____916 in
       Prims.strcat "?" uu____913)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____936 = FStar_Syntax_Subst.compress_univ u in
      match uu____936 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____946 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____953 =
      let uu____954 = FStar_Options.ugly () in Prims.op_Negation uu____954 in
    if uu____953
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____958 = FStar_Syntax_Subst.compress_univ u in
       match uu____958 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____970 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____970
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____972 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____972 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____986 = univ_to_string u2 in
                let uu____987 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____986 uu____987)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____991 =
             let uu____992 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____992 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____991
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____1005 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____1005 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____1018 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1018 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___207_1028  ->
    match uu___207_1028 with
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
        let uu____1030 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1030
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1033 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1033
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1044 =
          let uu____1045 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1045 in
        let uu____1048 =
          let uu____1049 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1049 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1044 uu____1048
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1068 =
          let uu____1069 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1069 in
        let uu____1072 =
          let uu____1073 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1073 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1068 uu____1072
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1083 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1083
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
    | uu____1093 ->
        let uu____1096 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1096 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1113 ->
        let uu____1116 = quals_to_string quals in Prims.strcat uu____1116 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1172 =
      let uu____1173 = FStar_Options.ugly () in Prims.op_Negation uu____1173 in
    if uu____1172
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1179 = FStar_Options.print_implicits () in
         if uu____1179 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1181 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1206,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1242 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1272 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1290  ->
                                 match uu____1290 with
                                 | (t1,uu____1296) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1272
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1242 (FStar_String.concat "\\/") in
           let uu____1301 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1301
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1313 = tag_of_term t in
           let uu____1314 = sli m in
           let uu____1315 = term_to_string t' in
           let uu____1316 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1313 uu____1314
             uu____1315 uu____1316
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1329 = tag_of_term t in
           let uu____1330 = term_to_string t' in
           let uu____1331 = sli m0 in
           let uu____1332 = sli m1 in
           let uu____1333 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1329
             uu____1330 uu____1331 uu____1332 uu____1333
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1335,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1349 = FStar_Range.string_of_range r in
           let uu____1350 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1349
             uu____1350
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1352) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1358 = db_to_string x3 in
           let uu____1359 =
             let uu____1360 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1360 in
           Prims.strcat uu____1358 uu____1359
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1364) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1391 = FStar_Options.print_universes () in
           if uu____1391
           then
             let uu____1392 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1392
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1412 = binders_to_string " -> " bs in
           let uu____1413 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1412 uu____1413
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1438 = binders_to_string " " bs in
                let uu____1439 = term_to_string t2 in
                let uu____1440 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1444 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1444) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1438 uu____1439
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1440
            | uu____1447 ->
                let uu____1450 = binders_to_string " " bs in
                let uu____1451 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1450 uu____1451)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1458 = bv_to_string xt in
           let uu____1459 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1462 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1458 uu____1459 uu____1462
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1487 = term_to_string t in
           let uu____1488 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1487 uu____1488
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1507 = lbs_to_string [] lbs in
           let uu____1508 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1507 uu____1508
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1569 =
                   let uu____1570 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1570
                     (FStar_Util.dflt "default") in
                 let uu____1575 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1569 uu____1575
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1591 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1591 in
           let uu____1592 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1592 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1631 = term_to_string head1 in
           let uu____1632 =
             let uu____1633 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1669  ->
                       match uu____1669 with
                       | (p,wopt,e) ->
                           let uu____1685 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1686 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1688 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1688 in
                           let uu____1689 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1685
                             uu____1686 uu____1689)) in
             FStar_Util.concat_l "\n\t|" uu____1633 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1631 uu____1632
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1696 = FStar_Options.print_universes () in
           if uu____1696
           then
             let uu____1697 = term_to_string t in
             let uu____1698 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1697 uu____1698
           else term_to_string t
       | uu____1700 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1702 =
      let uu____1703 = FStar_Options.ugly () in Prims.op_Negation uu____1703 in
    if uu____1702
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1725 = fv_to_string l in
           let uu____1726 =
             let uu____1727 =
               FStar_List.map
                 (fun uu____1738  ->
                    match uu____1738 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1727 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1725 uu____1726
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1750) ->
           let uu____1755 = FStar_Options.print_bound_var_types () in
           if uu____1755
           then
             let uu____1756 = bv_to_string x1 in
             let uu____1757 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1756 uu____1757
           else
             (let uu____1759 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1759)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1761 = FStar_Options.print_bound_var_types () in
           if uu____1761
           then
             let uu____1762 = bv_to_string x1 in
             let uu____1763 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1762 uu____1763
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1767 = FStar_Options.print_real_names () in
           if uu____1767
           then
             let uu____1768 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1768
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1787 = FStar_Options.print_universes () in
        if uu____1787
        then
          let uu____1794 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1812 =
                      let uu____1817 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1817 in
                    match uu____1812 with
                    | (us,td) ->
                        let uu____1820 =
                          let uu____1829 =
                            let uu____1830 = FStar_Syntax_Subst.compress td in
                            uu____1830.FStar_Syntax_Syntax.n in
                          match uu____1829 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1841,(t,uu____1843)::(d,uu____1845)::[])
                              -> (t, d)
                          | uu____1888 -> failwith "Impossibe" in
                        (match uu____1820 with
                         | (t,d) ->
                             let uu___214_1907 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___214_1907.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___214_1907.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1794)
        else lbs in
      let uu____1913 = quals_to_string' quals in
      let uu____1914 =
        let uu____1915 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1930 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1931 =
                    let uu____1932 = FStar_Options.print_universes () in
                    if uu____1932
                    then
                      let uu____1933 =
                        let uu____1934 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1934 ">" in
                      Prims.strcat "<" uu____1933
                    else "" in
                  let uu____1936 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1937 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1930 uu____1931
                    uu____1936 uu____1937)) in
        FStar_Util.concat_l "\n and " uu____1915 in
      FStar_Util.format3 "%slet %s %s" uu____1913
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1914
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1944 = FStar_Options.print_effect_args () in
    if uu____1944
    then
      let uu____1945 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1945
    else
      (let uu____1947 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1948 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1947 uu____1948)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___208_1950  ->
      match uu___208_1950 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1953 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1958 =
        let uu____1959 = FStar_Options.ugly () in
        Prims.op_Negation uu____1959 in
      if uu____1958
      then
        let uu____1960 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1960 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1966 = b in
         match uu____1966 with
         | (a,imp) ->
             let uu____1969 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1969
             then
               let uu____1970 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1970
             else
               (let uu____1972 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1974 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1974) in
                if uu____1972
                then
                  let uu____1975 = nm_to_string a in
                  imp_to_string uu____1975 imp
                else
                  (let uu____1977 =
                     let uu____1978 = nm_to_string a in
                     let uu____1979 =
                       let uu____1980 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1980 in
                     Prims.strcat uu____1978 uu____1979 in
                   imp_to_string uu____1977 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1986 = FStar_Options.print_implicits () in
        if uu____1986 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1988 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1988 (FStar_String.concat sep)
      else
        (let uu____1996 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1996 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___209_2003  ->
    match uu___209_2003 with
    | (a,imp) ->
        let uu____2016 = term_to_string a in imp_to_string uu____2016 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____2019 = FStar_Options.print_implicits () in
      if uu____2019 then args else filter_imp args in
    let uu____2023 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2023 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____2037 =
      let uu____2038 = FStar_Options.ugly () in Prims.op_Negation uu____2038 in
    if uu____2037
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2052 =
             let uu____2053 = FStar_Syntax_Subst.compress t in
             uu____2053.FStar_Syntax_Syntax.n in
           (match uu____2052 with
            | FStar_Syntax_Syntax.Tm_type uu____2056 when
                let uu____2057 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2057 -> term_to_string t
            | uu____2058 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2060 = univ_to_string u in
                     let uu____2061 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2060 uu____2061
                 | uu____2062 ->
                     let uu____2065 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2065))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2076 =
             let uu____2077 = FStar_Syntax_Subst.compress t in
             uu____2077.FStar_Syntax_Syntax.n in
           (match uu____2076 with
            | FStar_Syntax_Syntax.Tm_type uu____2080 when
                let uu____2081 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2081 -> term_to_string t
            | uu____2082 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2084 = univ_to_string u in
                     let uu____2085 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2084 uu____2085
                 | uu____2086 ->
                     let uu____2089 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2089))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2092 = FStar_Options.print_effect_args () in
             if uu____2092
             then
               let uu____2093 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2094 =
                 let uu____2095 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2095 (FStar_String.concat ", ") in
               let uu____2102 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2103 =
                 let uu____2104 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2104 (FStar_String.concat ", ") in
               let uu____2125 =
                 let uu____2126 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2126 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2093
                 uu____2094 uu____2102 uu____2103 uu____2125
             else
               (let uu____2136 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_2140  ->
                           match uu___210_2140 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2141 -> false)))
                    &&
                    (let uu____2143 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2143) in
                if uu____2136
                then
                  let uu____2144 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2144
                else
                  (let uu____2146 =
                     ((let uu____2149 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2149) &&
                        (let uu____2151 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2151))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2146
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2153 =
                        (let uu____2156 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2156) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2160  ->
                                   match uu___211_2160 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2161 -> false))) in
                      if uu____2153
                      then
                        let uu____2162 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2162
                      else
                        (let uu____2164 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2165 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2164 uu____2165)))) in
           let dec =
             let uu____2167 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2177  ->
                       match uu___212_2177 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2183 =
                             let uu____2184 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2184 in
                           [uu____2183]
                       | uu____2185 -> [])) in
             FStar_All.pipe_right uu____2167 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2189 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2199 = b in
    match uu____2199 with
    | (a,imp) ->
        let n1 =
          let uu____2203 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2203
          then FStar_Util.JsonNull
          else
            (let uu____2205 =
               let uu____2206 = nm_to_string a in
               imp_to_string uu____2206 imp in
             FStar_Util.JsonStr uu____2205) in
        let t =
          let uu____2208 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2208 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2225 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2225
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2232 = FStar_Options.print_universes () in
    if uu____2232 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2238 =
      let uu____2239 = FStar_Options.ugly () in Prims.op_Negation uu____2239 in
    if uu____2238
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2243 = s in
       match uu____2243 with
       | (us,t) ->
           let uu____2250 =
             let uu____2251 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2251 in
           let uu____2252 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2250 uu____2252)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2257 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2258 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2259 =
      let uu____2260 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2260 in
    let uu____2261 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2262 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2257 uu____2258 uu____2259
      uu____2261 uu____2262
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
          let uu____2283 =
            let uu____2284 = FStar_Options.ugly () in
            Prims.op_Negation uu____2284 in
          if uu____2283
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2296 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2296 (FStar_String.concat ",\n\t") in
             let uu____2305 =
               let uu____2308 =
                 let uu____2311 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2312 =
                   let uu____2315 =
                     let uu____2316 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2316 in
                   let uu____2317 =
                     let uu____2320 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2321 =
                       let uu____2324 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2325 =
                         let uu____2328 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2329 =
                           let uu____2332 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2333 =
                             let uu____2336 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2337 =
                               let uu____2340 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2341 =
                                 let uu____2344 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2345 =
                                   let uu____2348 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2349 =
                                     let uu____2352 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2353 =
                                       let uu____2356 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2357 =
                                         let uu____2360 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2361 =
                                           let uu____2364 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2365 =
                                             let uu____2368 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2369 =
                                               let uu____2372 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2373 =
                                                 let uu____2376 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2377 =
                                                   let uu____2380 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2380] in
                                                 uu____2376 :: uu____2377 in
                                               uu____2372 :: uu____2373 in
                                             uu____2368 :: uu____2369 in
                                           uu____2364 :: uu____2365 in
                                         uu____2360 :: uu____2361 in
                                       uu____2356 :: uu____2357 in
                                     uu____2352 :: uu____2353 in
                                   uu____2348 :: uu____2349 in
                                 uu____2344 :: uu____2345 in
                               uu____2340 :: uu____2341 in
                             uu____2336 :: uu____2337 in
                           uu____2332 :: uu____2333 in
                         uu____2328 :: uu____2329 in
                       uu____2324 :: uu____2325 in
                     uu____2320 :: uu____2321 in
                   uu____2315 :: uu____2317 in
                 uu____2311 :: uu____2312 in
               (if for_free then "_for_free " else "") :: uu____2308 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2305)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2394 =
      let uu____2395 = FStar_Options.ugly () in Prims.op_Negation uu____2395 in
    if uu____2394
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2401 -> ""
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
           (lid,univs1,tps,k,uu____2411,uu____2412) ->
           let uu____2421 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2422 = binders_to_string " " tps in
           let uu____2423 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2421
             lid.FStar_Ident.str uu____2422 uu____2423
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2427,uu____2428,uu____2429) ->
           let uu____2434 = FStar_Options.print_universes () in
           if uu____2434
           then
             let uu____2435 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2435 with
              | (univs2,t1) ->
                  let uu____2442 = univ_names_to_string univs2 in
                  let uu____2443 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2442
                    lid.FStar_Ident.str uu____2443)
           else
             (let uu____2445 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2445)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2449 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2449 with
            | (univs2,t1) ->
                let uu____2456 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2457 =
                  let uu____2458 = FStar_Options.print_universes () in
                  if uu____2458
                  then
                    let uu____2459 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2459
                  else "" in
                let uu____2461 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2456
                  lid.FStar_Ident.str uu____2457 uu____2461)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2463,f) ->
           let uu____2465 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2465
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2467) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2473 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2473
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2475) ->
           let uu____2484 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2484 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2502) -> lift_wp
             | (uu____2509,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2517 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2517 with
            | (us,t) ->
                let uu____2528 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2529 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2530 = univ_names_to_string us in
                let uu____2531 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2528
                  uu____2529 uu____2530 uu____2531)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2541 = FStar_Options.print_universes () in
           if uu____2541
           then
             let uu____2542 =
               let uu____2547 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2547 in
             (match uu____2542 with
              | (univs2,t) ->
                  let uu____2550 =
                    let uu____2563 =
                      let uu____2564 = FStar_Syntax_Subst.compress t in
                      uu____2564.FStar_Syntax_Syntax.n in
                    match uu____2563 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2605 -> failwith "impossible" in
                  (match uu____2550 with
                   | (tps1,c1) ->
                       let uu____2636 = sli l in
                       let uu____2637 = univ_names_to_string univs2 in
                       let uu____2638 = binders_to_string " " tps1 in
                       let uu____2639 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2636
                         uu____2637 uu____2638 uu____2639))
           else
             (let uu____2641 = sli l in
              let uu____2642 = binders_to_string " " tps in
              let uu____2643 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2641 uu____2642
                uu____2643))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2652 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2652 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2657,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2659;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2661;
                       FStar_Syntax_Syntax.lbdef = uu____2662;_}::[]),uu____2663)
        ->
        let uu____2686 = lbname_to_string lb in
        let uu____2687 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2686 uu____2687
    | uu____2688 ->
        let uu____2689 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2689 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2704 = sli m.FStar_Syntax_Syntax.name in
    let uu____2705 =
      let uu____2706 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2706 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2704 uu____2705
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___213_2714  ->
    match uu___213_2714 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2717 = FStar_Util.string_of_int i in
        let uu____2718 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2717 uu____2718
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2721 = bv_to_string x in
        let uu____2722 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2721 uu____2722
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2729 = bv_to_string x in
        let uu____2730 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2729 uu____2730
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2733 = FStar_Util.string_of_int i in
        let uu____2734 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2733 uu____2734
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2737 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2737
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2742 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2742 (FStar_String.concat "; ")
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
           (let uu____2814 = f x in
            FStar_Util.string_builder_append strb uu____2814);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2821 = f x1 in
                 FStar_Util.string_builder_append strb uu____2821)) xs;
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
           (let uu____2857 = f x in
            FStar_Util.string_builder_append strb uu____2857);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2864 = f x1 in
                 FStar_Util.string_builder_append strb uu____2864)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)