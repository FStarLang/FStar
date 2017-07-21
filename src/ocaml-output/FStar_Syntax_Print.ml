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
        let uu____829 = FStar_ST.read m in
        (match uu____829 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____842 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____847 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____858 = FStar_Options.hide_uvar_nums () in
    if uu____858
    then "?"
    else
      (let uu____860 =
         let uu____861 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____861 FStar_Util.string_of_int in
       Prims.strcat "?" uu____860)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____866 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____867 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____866 uu____867
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____872 = FStar_Options.hide_uvar_nums () in
    if uu____872
    then "?"
    else
      (let uu____874 =
         let uu____875 =
           let uu____876 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____876 FStar_Util.string_of_int in
         let uu____877 =
           let uu____878 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____878 in
         Prims.strcat uu____875 uu____877 in
       Prims.strcat "?" uu____874)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____897 = FStar_Syntax_Subst.compress_univ u in
      match uu____897 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____907 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____914 =
      let uu____915 = FStar_Options.ugly () in Prims.op_Negation uu____915 in
    if uu____914
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____919 = FStar_Syntax_Subst.compress_univ u in
       match uu____919 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____931 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____931
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____933 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____933 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____947 = univ_to_string u2 in
                let uu____948 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____947 uu____948)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____952 =
             let uu____953 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____953 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____952
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____966 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____966 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____979 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____979 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___203_989  ->
    match uu___203_989 with
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
        let uu____991 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____991
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____994 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____994 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1005 =
          let uu____1006 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1006 in
        let uu____1009 =
          let uu____1010 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1010 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1005 uu____1009
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1029 =
          let uu____1030 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1030 in
        let uu____1033 =
          let uu____1034 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1034 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1029 uu____1033
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1044 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1044
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
    | uu____1054 ->
        let uu____1057 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1057 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1074 ->
        let uu____1077 = quals_to_string quals in Prims.strcat uu____1077 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1133 =
      let uu____1134 = FStar_Options.ugly () in Prims.op_Negation uu____1134 in
    if uu____1133
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1140 = FStar_Options.print_implicits () in
         if uu____1140 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1142 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1167,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1203 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1233 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1251  ->
                                 match uu____1251 with
                                 | (t1,uu____1257) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1233
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1203 (FStar_String.concat "\\/") in
           let uu____1262 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1262
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1274 = tag_of_term t in
           let uu____1275 = sli m in
           let uu____1276 = term_to_string t' in
           let uu____1277 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1274 uu____1275
             uu____1276 uu____1277
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1290 = tag_of_term t in
           let uu____1291 = term_to_string t' in
           let uu____1292 = sli m0 in
           let uu____1293 = sli m1 in
           let uu____1294 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1290
             uu____1291 uu____1292 uu____1293 uu____1294
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1296,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1310 = FStar_Range.string_of_range r in
           let uu____1311 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1310
             uu____1311
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1313) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1319 = db_to_string x3 in
           let uu____1320 =
             let uu____1321 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1321 in
           Prims.strcat uu____1319 uu____1320
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1325) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1352 = FStar_Options.print_universes () in
           if uu____1352
           then
             let uu____1353 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1353
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1373 = binders_to_string " -> " bs in
           let uu____1374 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1373 uu____1374
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1399 = binders_to_string " " bs in
                let uu____1400 = term_to_string t2 in
                let uu____1401 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1405 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1405) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1399 uu____1400
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1401
            | uu____1408 ->
                let uu____1411 = binders_to_string " " bs in
                let uu____1412 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1411 uu____1412)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1419 = bv_to_string xt in
           let uu____1420 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1423 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1419 uu____1420 uu____1423
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1448 = term_to_string t in
           let uu____1449 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1448 uu____1449
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1468 = lbs_to_string [] lbs in
           let uu____1469 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1468 uu____1469
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1530 =
                   let uu____1531 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1531
                     (FStar_Util.dflt "default") in
                 let uu____1536 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1530 uu____1536
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1552 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1552 in
           let uu____1553 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1553 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1592 = term_to_string head1 in
           let uu____1593 =
             let uu____1594 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1630  ->
                       match uu____1630 with
                       | (p,wopt,e) ->
                           let uu____1646 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1647 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1649 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1649 in
                           let uu____1650 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1646
                             uu____1647 uu____1650)) in
             FStar_Util.concat_l "\n\t|" uu____1594 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1592 uu____1593
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1657 = FStar_Options.print_universes () in
           if uu____1657
           then
             let uu____1658 = term_to_string t in
             let uu____1659 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1658 uu____1659
           else term_to_string t
       | uu____1661 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1663 =
      let uu____1664 = FStar_Options.ugly () in Prims.op_Negation uu____1664 in
    if uu____1663
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1686 = fv_to_string l in
           let uu____1687 =
             let uu____1688 =
               FStar_List.map
                 (fun uu____1699  ->
                    match uu____1699 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1688 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1686 uu____1687
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1711) ->
           let uu____1716 = FStar_Options.print_bound_var_types () in
           if uu____1716
           then
             let uu____1717 = bv_to_string x1 in
             let uu____1718 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1717 uu____1718
           else
             (let uu____1720 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1720)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1722 = FStar_Options.print_bound_var_types () in
           if uu____1722
           then
             let uu____1723 = bv_to_string x1 in
             let uu____1724 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1723 uu____1724
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1728 = FStar_Options.print_real_names () in
           if uu____1728
           then
             let uu____1729 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1729
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1748 = FStar_Options.print_universes () in
        if uu____1748
        then
          let uu____1755 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1773 =
                      let uu____1778 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1778 in
                    match uu____1773 with
                    | (us,td) ->
                        let uu____1781 =
                          let uu____1790 =
                            let uu____1791 = FStar_Syntax_Subst.compress td in
                            uu____1791.FStar_Syntax_Syntax.n in
                          match uu____1790 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1802,(t,uu____1804)::(d,uu____1806)::[])
                              -> (t, d)
                          | uu____1849 -> failwith "Impossibe" in
                        (match uu____1781 with
                         | (t,d) ->
                             let uu___210_1868 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___210_1868.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___210_1868.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1755)
        else lbs in
      let uu____1874 = quals_to_string' quals in
      let uu____1875 =
        let uu____1876 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1891 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1892 =
                    let uu____1893 = FStar_Options.print_universes () in
                    if uu____1893
                    then
                      let uu____1894 =
                        let uu____1895 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1895 ">" in
                      Prims.strcat "<" uu____1894
                    else "" in
                  let uu____1897 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1898 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1891 uu____1892
                    uu____1897 uu____1898)) in
        FStar_Util.concat_l "\n and " uu____1876 in
      FStar_Util.format3 "%slet %s %s" uu____1874
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1875
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1905 = FStar_Options.print_effect_args () in
    if uu____1905
    then
      let uu____1906 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1906
    else
      (let uu____1908 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1909 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1908 uu____1909)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___204_1911  ->
      match uu___204_1911 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1914 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1919 =
        let uu____1920 = FStar_Options.ugly () in
        Prims.op_Negation uu____1920 in
      if uu____1919
      then
        let uu____1921 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1921 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1927 = b in
         match uu____1927 with
         | (a,imp) ->
             let uu____1930 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1930
             then
               let uu____1931 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1931
             else
               (let uu____1933 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1935 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1935) in
                if uu____1933
                then
                  let uu____1936 = nm_to_string a in
                  imp_to_string uu____1936 imp
                else
                  (let uu____1938 =
                     let uu____1939 = nm_to_string a in
                     let uu____1940 =
                       let uu____1941 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1941 in
                     Prims.strcat uu____1939 uu____1940 in
                   imp_to_string uu____1938 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1947 = FStar_Options.print_implicits () in
        if uu____1947 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1949 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1949 (FStar_String.concat sep)
      else
        (let uu____1957 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1957 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___205_1964  ->
    match uu___205_1964 with
    | (a,imp) ->
        let uu____1977 = term_to_string a in imp_to_string uu____1977 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1980 = FStar_Options.print_implicits () in
      if uu____1980 then args else filter_imp args in
    let uu____1984 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1984 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1998 =
      let uu____1999 = FStar_Options.ugly () in Prims.op_Negation uu____1999 in
    if uu____1998
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2013 =
             let uu____2014 = FStar_Syntax_Subst.compress t in
             uu____2014.FStar_Syntax_Syntax.n in
           (match uu____2013 with
            | FStar_Syntax_Syntax.Tm_type uu____2017 when
                let uu____2018 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2018 -> term_to_string t
            | uu____2019 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2021 = univ_to_string u in
                     let uu____2022 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2021 uu____2022
                 | uu____2023 ->
                     let uu____2026 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2026))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2037 =
             let uu____2038 = FStar_Syntax_Subst.compress t in
             uu____2038.FStar_Syntax_Syntax.n in
           (match uu____2037 with
            | FStar_Syntax_Syntax.Tm_type uu____2041 when
                let uu____2042 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2042 -> term_to_string t
            | uu____2043 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2045 = univ_to_string u in
                     let uu____2046 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2045 uu____2046
                 | uu____2047 ->
                     let uu____2050 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2050))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2053 = FStar_Options.print_effect_args () in
             if uu____2053
             then
               let uu____2054 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2055 =
                 let uu____2056 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2056 (FStar_String.concat ", ") in
               let uu____2063 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2064 =
                 let uu____2065 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2065 (FStar_String.concat ", ") in
               let uu____2086 =
                 let uu____2087 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2087 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2054
                 uu____2055 uu____2063 uu____2064 uu____2086
             else
               (let uu____2097 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___206_2101  ->
                           match uu___206_2101 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2102 -> false)))
                    &&
                    (let uu____2104 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2104) in
                if uu____2097
                then
                  let uu____2105 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2105
                else
                  (let uu____2107 =
                     ((let uu____2110 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2110) &&
                        (let uu____2112 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2112))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2107
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2114 =
                        (let uu____2117 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2117) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___207_2121  ->
                                   match uu___207_2121 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2122 -> false))) in
                      if uu____2114
                      then
                        let uu____2123 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2123
                      else
                        (let uu____2125 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2126 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2125 uu____2126)))) in
           let dec =
             let uu____2128 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___208_2138  ->
                       match uu___208_2138 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2144 =
                             let uu____2145 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2145 in
                           [uu____2144]
                       | uu____2146 -> [])) in
             FStar_All.pipe_right uu____2128 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2150 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2160 = FStar_Options.print_universes () in
    if uu____2160 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2166 =
      let uu____2167 = FStar_Options.ugly () in Prims.op_Negation uu____2167 in
    if uu____2166
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2171 = s in
       match uu____2171 with
       | (us,t) ->
           let uu____2178 =
             let uu____2179 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2179 in
           let uu____2180 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2178 uu____2180)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2185 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2186 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2187 =
      let uu____2188 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2188 in
    let uu____2189 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2190 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2185 uu____2186 uu____2187
      uu____2189 uu____2190
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
          let uu____2211 =
            let uu____2212 = FStar_Options.ugly () in
            Prims.op_Negation uu____2212 in
          if uu____2211
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2224 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2224 (FStar_String.concat ",\n\t") in
             let uu____2233 =
               let uu____2236 =
                 let uu____2239 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2240 =
                   let uu____2243 =
                     let uu____2244 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2244 in
                   let uu____2245 =
                     let uu____2248 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2249 =
                       let uu____2252 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2253 =
                         let uu____2256 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2257 =
                           let uu____2260 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2261 =
                             let uu____2264 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2265 =
                               let uu____2268 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2269 =
                                 let uu____2272 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2273 =
                                   let uu____2276 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2277 =
                                     let uu____2280 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2281 =
                                       let uu____2284 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2285 =
                                         let uu____2288 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2289 =
                                           let uu____2292 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2293 =
                                             let uu____2296 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2297 =
                                               let uu____2300 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2301 =
                                                 let uu____2304 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2305 =
                                                   let uu____2308 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2308] in
                                                 uu____2304 :: uu____2305 in
                                               uu____2300 :: uu____2301 in
                                             uu____2296 :: uu____2297 in
                                           uu____2292 :: uu____2293 in
                                         uu____2288 :: uu____2289 in
                                       uu____2284 :: uu____2285 in
                                     uu____2280 :: uu____2281 in
                                   uu____2276 :: uu____2277 in
                                 uu____2272 :: uu____2273 in
                               uu____2268 :: uu____2269 in
                             uu____2264 :: uu____2265 in
                           uu____2260 :: uu____2261 in
                         uu____2256 :: uu____2257 in
                       uu____2252 :: uu____2253 in
                     uu____2248 :: uu____2249 in
                   uu____2243 :: uu____2245 in
                 uu____2239 :: uu____2240 in
               (if for_free then "_for_free " else "") :: uu____2236 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2233)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2322 =
      let uu____2323 = FStar_Options.ugly () in Prims.op_Negation uu____2323 in
    if uu____2322
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2329 -> ""
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
           (lid,univs1,tps,k,uu____2339,uu____2340) ->
           let uu____2349 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2350 = binders_to_string " " tps in
           let uu____2351 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2349
             lid.FStar_Ident.str uu____2350 uu____2351
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2355,uu____2356,uu____2357) ->
           let uu____2362 = FStar_Options.print_universes () in
           if uu____2362
           then
             let uu____2363 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2363 with
              | (univs2,t1) ->
                  let uu____2370 = univ_names_to_string univs2 in
                  let uu____2371 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2370
                    lid.FStar_Ident.str uu____2371)
           else
             (let uu____2373 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2373)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2377 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2377 with
            | (univs2,t1) ->
                let uu____2384 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2385 =
                  let uu____2386 = FStar_Options.print_universes () in
                  if uu____2386
                  then
                    let uu____2387 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2387
                  else "" in
                let uu____2389 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2384
                  lid.FStar_Ident.str uu____2385 uu____2389)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2391,f) ->
           let uu____2393 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2393
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2395) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2401 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2401
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2403) ->
           let uu____2412 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2412 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2430) -> lift_wp
             | (uu____2437,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2445 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2445 with
            | (us,t) ->
                let uu____2456 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2457 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2458 = univ_names_to_string us in
                let uu____2459 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2456
                  uu____2457 uu____2458 uu____2459)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2469 = FStar_Options.print_universes () in
           if uu____2469
           then
             let uu____2470 =
               let uu____2475 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2475 in
             (match uu____2470 with
              | (univs2,t) ->
                  let uu____2478 =
                    let uu____2491 =
                      let uu____2492 = FStar_Syntax_Subst.compress t in
                      uu____2492.FStar_Syntax_Syntax.n in
                    match uu____2491 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2533 -> failwith "impossible" in
                  (match uu____2478 with
                   | (tps1,c1) ->
                       let uu____2564 = sli l in
                       let uu____2565 = univ_names_to_string univs2 in
                       let uu____2566 = binders_to_string " " tps1 in
                       let uu____2567 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2564
                         uu____2565 uu____2566 uu____2567))
           else
             (let uu____2569 = sli l in
              let uu____2570 = binders_to_string " " tps in
              let uu____2571 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2569 uu____2570
                uu____2571))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2580 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2580 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2585,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2587;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2589;
                       FStar_Syntax_Syntax.lbdef = uu____2590;_}::[]),uu____2591)
        ->
        let uu____2614 = lbname_to_string lb in
        let uu____2615 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2614 uu____2615
    | uu____2616 ->
        let uu____2617 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2617 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2632 = sli m.FStar_Syntax_Syntax.name in
    let uu____2633 =
      let uu____2634 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2634 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2632 uu____2633
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___209_2642  ->
    match uu___209_2642 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2645 = FStar_Util.string_of_int i in
        let uu____2646 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2645 uu____2646
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2649 = bv_to_string x in
        let uu____2650 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2649 uu____2650
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2657 = bv_to_string x in
        let uu____2658 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2657 uu____2658
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2661 = FStar_Util.string_of_int i in
        let uu____2662 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2661 uu____2662
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2665 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2665
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2670 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2670 (FStar_String.concat "; ")
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
           (let uu____2742 = f x in
            FStar_Util.string_builder_append strb uu____2742);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2749 = f x1 in
                 FStar_Util.string_builder_append strb uu____2749)) xs;
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
           (let uu____2785 = f x in
            FStar_Util.string_builder_append strb uu____2785);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2792 = f x1 in
                 FStar_Util.string_builder_append strb uu____2792)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)