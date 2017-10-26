open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___209_4  ->
    match uu___209_4 with
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
  fun uu___210_261  ->
    match uu___210_261 with
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
         (fun uu___211_326  ->
            match uu___211_326 with
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
  fun x  -> FStar_Parser_Const.const_to_string x
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___212_599  ->
    match uu___212_599 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____607 = db_to_string x in Prims.strcat "Tm_bvar: " uu____607
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____609 = nm_to_string x in Prims.strcat "Tm_name: " uu____609
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____611 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____611
    | FStar_Syntax_Syntax.Tm_uinst uu____612 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____619 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____620 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____621 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____638 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____651 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____658 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____673 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____696 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____723 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____736 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____753,m) ->
        let uu____795 = FStar_ST.op_Bang m in
        (match uu____795 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____870 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____875 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____886 = FStar_Options.hide_uvar_nums () in
    if uu____886
    then "?"
    else
      (let uu____888 =
         let uu____889 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____889 FStar_Util.string_of_int in
       Prims.strcat "?" uu____888)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____894 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____895 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____894 uu____895
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____900 = FStar_Options.hide_uvar_nums () in
    if uu____900
    then "?"
    else
      (let uu____902 =
         let uu____903 =
           let uu____904 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____904 FStar_Util.string_of_int in
         let uu____905 =
           let uu____906 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____906 in
         Prims.strcat uu____903 uu____905 in
       Prims.strcat "?" uu____902)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____925 = FStar_Syntax_Subst.compress_univ u in
      match uu____925 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____935 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____942 =
      let uu____943 = FStar_Options.ugly () in Prims.op_Negation uu____943 in
    if uu____942
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____947 = FStar_Syntax_Subst.compress_univ u in
       match uu____947 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____959 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____959
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____961 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____961 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____975 = univ_to_string u2 in
                let uu____976 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____975 uu____976)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____980 =
             let uu____981 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____981 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____980
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____994 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____994 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____1007 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1007 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___213_1017  ->
    match uu___213_1017 with
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
        let uu____1019 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1019
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1022 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1022
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1033 =
          let uu____1034 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1034 in
        let uu____1037 =
          let uu____1038 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1038 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1033 uu____1037
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1057 =
          let uu____1058 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1058 in
        let uu____1061 =
          let uu____1062 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1062 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1057 uu____1061
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1072 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1072
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
    | uu____1082 ->
        let uu____1085 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1085 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1102 ->
        let uu____1105 = quals_to_string quals in Prims.strcat uu____1105 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1161 =
      let uu____1162 = FStar_Options.ugly () in Prims.op_Negation uu____1162 in
    if uu____1161
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1168 = FStar_Options.print_implicits () in
         if uu____1168 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1170 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1195,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1231 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1261 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1279  ->
                                 match uu____1279 with
                                 | (t1,uu____1285) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1261
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1231 (FStar_String.concat "\\/") in
           let uu____1290 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1290
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1302 = tag_of_term t in
           let uu____1303 = sli m in
           let uu____1304 = term_to_string t' in
           let uu____1305 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1302 uu____1303
             uu____1304 uu____1305
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1318 = tag_of_term t in
           let uu____1319 = term_to_string t' in
           let uu____1320 = sli m0 in
           let uu____1321 = sli m1 in
           let uu____1322 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1318
             uu____1319 uu____1320 uu____1321 uu____1322
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1324,s,uu____1326)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1343 = FStar_Range.string_of_range r in
           let uu____1344 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1343
             uu____1344
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1351 = lid_to_string l in
           let uu____1352 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1353 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1351 uu____1352
             uu____1353
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1355) ->
           let uu____1360 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1360
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1362 = db_to_string x3 in
           let uu____1363 =
             let uu____1364 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1364 in
           Prims.strcat uu____1362 uu____1363
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1368) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1395 = FStar_Options.print_universes () in
           if uu____1395
           then
             let uu____1396 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1396
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1416 = binders_to_string " -> " bs in
           let uu____1417 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1416 uu____1417
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1442 = binders_to_string " " bs in
                let uu____1443 = term_to_string t2 in
                let uu____1444 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1448 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1448) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1442 uu____1443
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1444
            | uu____1451 ->
                let uu____1454 = binders_to_string " " bs in
                let uu____1455 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1454 uu____1455)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1462 = bv_to_string xt in
           let uu____1463 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1466 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1462 uu____1463 uu____1466
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1491 = term_to_string t in
           let uu____1492 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1491 uu____1492
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1511 = lbs_to_string [] lbs in
           let uu____1512 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1511 uu____1512
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1573 =
                   let uu____1574 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1574
                     (FStar_Util.dflt "default") in
                 let uu____1579 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1573 uu____1579
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1595 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1595 in
           let uu____1596 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1596 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1635 = term_to_string head1 in
           let uu____1636 =
             let uu____1637 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1673  ->
                       match uu____1673 with
                       | (p,wopt,e) ->
                           let uu____1689 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1690 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1692 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1692 in
                           let uu____1693 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1689
                             uu____1690 uu____1693)) in
             FStar_Util.concat_l "\n\t|" uu____1637 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1635 uu____1636
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1700 = FStar_Options.print_universes () in
           if uu____1700
           then
             let uu____1701 = term_to_string t in
             let uu____1702 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1701 uu____1702
           else term_to_string t
       | uu____1704 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1706 =
      let uu____1707 = FStar_Options.ugly () in Prims.op_Negation uu____1707 in
    if uu____1706
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1729 = fv_to_string l in
           let uu____1730 =
             let uu____1731 =
               FStar_List.map
                 (fun uu____1742  ->
                    match uu____1742 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1731 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1729 uu____1730
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1754) ->
           let uu____1759 = FStar_Options.print_bound_var_types () in
           if uu____1759
           then
             let uu____1760 = bv_to_string x1 in
             let uu____1761 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1760 uu____1761
           else
             (let uu____1763 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1763)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1765 = FStar_Options.print_bound_var_types () in
           if uu____1765
           then
             let uu____1766 = bv_to_string x1 in
             let uu____1767 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1766 uu____1767
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1771 = FStar_Options.print_real_names () in
           if uu____1771
           then
             let uu____1772 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1772
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1791 = FStar_Options.print_universes () in
        if uu____1791
        then
          let uu____1798 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1816 =
                      let uu____1821 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1821 in
                    match uu____1816 with
                    | (us,td) ->
                        let uu____1824 =
                          let uu____1833 =
                            let uu____1834 = FStar_Syntax_Subst.compress td in
                            uu____1834.FStar_Syntax_Syntax.n in
                          match uu____1833 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1845,(t,uu____1847)::(d,uu____1849)::[])
                              -> (t, d)
                          | uu____1892 -> failwith "Impossibe" in
                        (match uu____1824 with
                         | (t,d) ->
                             let uu___220_1911 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___220_1911.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___220_1911.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1798)
        else lbs in
      let uu____1917 = quals_to_string' quals in
      let uu____1918 =
        let uu____1919 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1934 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1935 =
                    let uu____1936 = FStar_Options.print_universes () in
                    if uu____1936
                    then
                      let uu____1937 =
                        let uu____1938 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1938 ">" in
                      Prims.strcat "<" uu____1937
                    else "" in
                  let uu____1940 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1941 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1934 uu____1935
                    uu____1940 uu____1941)) in
        FStar_Util.concat_l "\n and " uu____1919 in
      FStar_Util.format3 "%slet %s %s" uu____1917
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1918
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1948 = FStar_Options.print_effect_args () in
    if uu____1948
    then
      let uu____1949 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1949
    else
      (let uu____1951 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1952 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1951 uu____1952)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___214_1954  ->
      match uu___214_1954 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1957 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1962 =
        let uu____1963 = FStar_Options.ugly () in
        Prims.op_Negation uu____1963 in
      if uu____1962
      then
        let uu____1964 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1964 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1970 = b in
         match uu____1970 with
         | (a,imp) ->
             let uu____1973 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1973
             then
               let uu____1974 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1974
             else
               (let uu____1976 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1978 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1978) in
                if uu____1976
                then
                  let uu____1979 = nm_to_string a in
                  imp_to_string uu____1979 imp
                else
                  (let uu____1981 =
                     let uu____1982 = nm_to_string a in
                     let uu____1983 =
                       let uu____1984 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1984 in
                     Prims.strcat uu____1982 uu____1983 in
                   imp_to_string uu____1981 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1990 = FStar_Options.print_implicits () in
        if uu____1990 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1992 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1992 (FStar_String.concat sep)
      else
        (let uu____2000 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____2000 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___215_2007  ->
    match uu___215_2007 with
    | (a,imp) ->
        let uu____2020 = term_to_string a in imp_to_string uu____2020 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____2023 = FStar_Options.print_implicits () in
      if uu____2023 then args else filter_imp args in
    let uu____2027 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2027 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____2041 =
      let uu____2042 = FStar_Options.ugly () in Prims.op_Negation uu____2042 in
    if uu____2041
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2056 =
             let uu____2057 = FStar_Syntax_Subst.compress t in
             uu____2057.FStar_Syntax_Syntax.n in
           (match uu____2056 with
            | FStar_Syntax_Syntax.Tm_type uu____2060 when
                let uu____2061 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2061 -> term_to_string t
            | uu____2062 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2064 = univ_to_string u in
                     let uu____2065 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2064 uu____2065
                 | uu____2066 ->
                     let uu____2069 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2069))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
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
                     FStar_Util.format2 "GTot<%s> %s" uu____2088 uu____2089
                 | uu____2090 ->
                     let uu____2093 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2093))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2096 = FStar_Options.print_effect_args () in
             if uu____2096
             then
               let uu____2097 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2098 =
                 let uu____2099 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2099 (FStar_String.concat ", ") in
               let uu____2106 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2107 =
                 let uu____2108 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2108 (FStar_String.concat ", ") in
               let uu____2129 =
                 let uu____2130 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2130 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2097
                 uu____2098 uu____2106 uu____2107 uu____2129
             else
               (let uu____2140 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___216_2144  ->
                           match uu___216_2144 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2145 -> false)))
                    &&
                    (let uu____2147 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2147) in
                if uu____2140
                then
                  let uu____2148 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2148
                else
                  (let uu____2150 =
                     ((let uu____2153 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2153) &&
                        (let uu____2155 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2155))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2150
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2157 =
                        (let uu____2160 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2160) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___217_2164  ->
                                   match uu___217_2164 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2165 -> false))) in
                      if uu____2157
                      then
                        let uu____2166 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2166
                      else
                        (let uu____2168 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2169 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2168 uu____2169)))) in
           let dec =
             let uu____2171 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___218_2181  ->
                       match uu___218_2181 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2187 =
                             let uu____2188 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2188 in
                           [uu____2187]
                       | uu____2189 -> [])) in
             FStar_All.pipe_right uu____2171 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2193 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2203 = b in
    match uu____2203 with
    | (a,imp) ->
        let n1 =
          let uu____2207 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2207
          then FStar_Util.JsonNull
          else
            (let uu____2209 =
               let uu____2210 = nm_to_string a in
               imp_to_string uu____2210 imp in
             FStar_Util.JsonStr uu____2209) in
        let t =
          let uu____2212 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2212 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2229 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2229
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2236 = FStar_Options.print_universes () in
    if uu____2236 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2242 =
      let uu____2243 = FStar_Options.ugly () in Prims.op_Negation uu____2243 in
    if uu____2242
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2247 = s in
       match uu____2247 with
       | (us,t) ->
           let uu____2254 =
             let uu____2255 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2255 in
           let uu____2256 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2254 uu____2256)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2261 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2262 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2263 =
      let uu____2264 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2264 in
    let uu____2265 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2266 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2261 uu____2262 uu____2263
      uu____2265 uu____2266
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
          let uu____2287 =
            let uu____2288 = FStar_Options.ugly () in
            Prims.op_Negation uu____2288 in
          if uu____2287
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2300 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2300 (FStar_String.concat ",\n\t") in
             let uu____2309 =
               let uu____2312 =
                 let uu____2315 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2316 =
                   let uu____2319 =
                     let uu____2320 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2320 in
                   let uu____2321 =
                     let uu____2324 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2325 =
                       let uu____2328 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2329 =
                         let uu____2332 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2333 =
                           let uu____2336 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2337 =
                             let uu____2340 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2341 =
                               let uu____2344 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2345 =
                                 let uu____2348 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2349 =
                                   let uu____2352 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2353 =
                                     let uu____2356 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2357 =
                                       let uu____2360 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2361 =
                                         let uu____2364 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2365 =
                                           let uu____2368 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2369 =
                                             let uu____2372 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2373 =
                                               let uu____2376 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2377 =
                                                 let uu____2380 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2381 =
                                                   let uu____2384 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2384] in
                                                 uu____2380 :: uu____2381 in
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
                   uu____2319 :: uu____2321 in
                 uu____2315 :: uu____2316 in
               (if for_free then "_for_free " else "") :: uu____2312 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2309)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2398 =
      let uu____2399 = FStar_Options.ugly () in Prims.op_Negation uu____2399 in
    if uu____2398
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2405 -> ""
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
           (lid,univs1,tps,k,uu____2415,uu____2416) ->
           let uu____2425 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2426 = binders_to_string " " tps in
           let uu____2427 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2425
             lid.FStar_Ident.str uu____2426 uu____2427
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2431,uu____2432,uu____2433) ->
           let uu____2438 = FStar_Options.print_universes () in
           if uu____2438
           then
             let uu____2439 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2439 with
              | (univs2,t1) ->
                  let uu____2446 = univ_names_to_string univs2 in
                  let uu____2447 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2446
                    lid.FStar_Ident.str uu____2447)
           else
             (let uu____2449 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2449)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2453 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2453 with
            | (univs2,t1) ->
                let uu____2460 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2461 =
                  let uu____2462 = FStar_Options.print_universes () in
                  if uu____2462
                  then
                    let uu____2463 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2463
                  else "" in
                let uu____2465 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2460
                  lid.FStar_Ident.str uu____2461 uu____2465)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2467,f) ->
           let uu____2469 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2469
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2471) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2477 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2477
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2479) ->
           let uu____2488 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2488 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2506) -> lift_wp
             | (uu____2513,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2521 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2521 with
            | (us,t) ->
                let uu____2532 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2533 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2534 = univ_names_to_string us in
                let uu____2535 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2532
                  uu____2533 uu____2534 uu____2535)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2545 = FStar_Options.print_universes () in
           if uu____2545
           then
             let uu____2546 =
               let uu____2551 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2551 in
             (match uu____2546 with
              | (univs2,t) ->
                  let uu____2554 =
                    let uu____2567 =
                      let uu____2568 = FStar_Syntax_Subst.compress t in
                      uu____2568.FStar_Syntax_Syntax.n in
                    match uu____2567 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2609 -> failwith "impossible" in
                  (match uu____2554 with
                   | (tps1,c1) ->
                       let uu____2640 = sli l in
                       let uu____2641 = univ_names_to_string univs2 in
                       let uu____2642 = binders_to_string " " tps1 in
                       let uu____2643 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2640
                         uu____2641 uu____2642 uu____2643))
           else
             (let uu____2645 = sli l in
              let uu____2646 = binders_to_string " " tps in
              let uu____2647 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2645 uu____2646
                uu____2647))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2656 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2656 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2661,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2663;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2665;
                       FStar_Syntax_Syntax.lbdef = uu____2666;_}::[]),uu____2667)
        ->
        let uu____2690 = lbname_to_string lb in
        let uu____2691 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2690 uu____2691
    | uu____2692 ->
        let uu____2693 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2693 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2708 = sli m.FStar_Syntax_Syntax.name in
    let uu____2709 =
      let uu____2710 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2710 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2708 uu____2709
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___219_2718  ->
    match uu___219_2718 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2721 = FStar_Util.string_of_int i in
        let uu____2722 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2721 uu____2722
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2725 = bv_to_string x in
        let uu____2726 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2725 uu____2726
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2733 = bv_to_string x in
        let uu____2734 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2733 uu____2734
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2737 = FStar_Util.string_of_int i in
        let uu____2738 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2737 uu____2738
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2741 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2741
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2746 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2746 (FStar_String.concat "; ")
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
           (let uu____2818 = f x in
            FStar_Util.string_builder_append strb uu____2818);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2825 = f x1 in
                 FStar_Util.string_builder_append strb uu____2825)) xs;
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
           (let uu____2861 = f x in
            FStar_Util.string_builder_append strb uu____2861);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2868 = f x1 in
                 FStar_Util.string_builder_append strb uu____2868)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)