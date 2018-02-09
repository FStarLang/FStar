open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___65_3  ->
    match uu___65_3 with
    | FStar_Syntax_Syntax.Delta_constant  -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____5 = FStar_Util.string_of_int i in
        Prims.strcat "Delta_defined_at_level " uu____5
    | FStar_Syntax_Syntax.Delta_equational  -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____7 =
          let uu____8 = delta_depth_to_string d in Prims.strcat uu____8 ")" in
        Prims.strcat "Delta_abstract (" uu____7
let sli: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____12 = FStar_Options.print_real_names () in
    if uu____12
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let lid_to_string: FStar_Ident.lid -> Prims.string = fun l  -> sli l
let fv_to_string: FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let bv_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____23 =
      let uu____24 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____24 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____23
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____28 = FStar_Options.print_real_names () in
    if uu____28
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____33 =
      let uu____34 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____34 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____33
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
      | uu____168 -> false
let get_lid:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____177 -> failwith "get_lid"
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
  'Auu____232 'Auu____233 .
    ('Auu____233,'Auu____232) FStar_Util.either -> Prims.bool
  =
  fun uu___66_241  ->
    match uu___66_241 with
    | FStar_Util.Inl uu____246 -> false
    | FStar_Util.Inr uu____247 -> true
let filter_imp:
  'Auu____250 .
    ('Auu____250,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____250,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___67_304  ->
            match uu___67_304 with
            | (uu____311,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____312)) -> false
            | uu____315 -> true))
let rec reconstruct_lex:
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____331 =
      let uu____332 = FStar_Syntax_Subst.compress e in
      uu____332.FStar_Syntax_Syntax.n in
    match uu____331 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____395 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____395
        then
          let uu____404 =
            let uu____411 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____411 in
          (match uu____404 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____429 =
                 let uu____434 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____434 :: xs in
               FStar_Pervasives_Native.Some uu____429
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____458 ->
        let uu____459 = is_lex_top e in
        if uu____459
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find: 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____503 = f hd1 in if uu____503 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____523 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____523
let infix_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____545 = get_lid e in find_lid uu____545 infix_prim_ops
let unary_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____553 = get_lid e in find_lid uu____553 unary_prim_ops
let quant_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun t  -> let uu____561 = get_lid t in find_lid uu____561 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  -> FStar_Parser_Const.const_to_string x
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___68_567  ->
    match uu___68_567 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____573 = FStar_Options.hide_uvar_nums () in
    if uu____573
    then "?"
    else
      (let uu____575 =
         let uu____576 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____576 FStar_Util.string_of_int in
       Prims.strcat "?" uu____575)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____580 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____581 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____580 uu____581
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____585 = FStar_Options.hide_uvar_nums () in
    if uu____585
    then "?"
    else
      (let uu____587 =
         let uu____588 =
           let uu____589 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____589 FStar_Util.string_of_int in
         let uu____590 =
           let uu____591 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____591 in
         Prims.strcat uu____588 uu____590 in
       Prims.strcat "?" uu____587)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____608 = FStar_Syntax_Subst.compress_univ u in
      match uu____608 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____618 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____624 = FStar_Syntax_Subst.compress_univ u in
    match uu____624 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____634 = univ_uvar_to_string u1 in
        Prims.strcat "U_unif " uu____634
    | FStar_Syntax_Syntax.U_name x ->
        Prims.strcat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____637 = FStar_Util.string_of_int x in
        Prims.strcat "@" uu____637
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____639 = int_of_univ (Prims.parse_int "1") u1 in
        (match uu____639 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____653 = univ_to_string u2 in
             let uu____654 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "(%s + %s)" uu____653 uu____654)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____658 =
          let uu____659 = FStar_List.map univ_to_string us in
          FStar_All.pipe_right uu____659 (FStar_String.concat ", ") in
        FStar_Util.format1 "(max %s)" uu____658
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
let univs_to_string: FStar_Syntax_Syntax.universes -> Prims.string =
  fun us  ->
    let uu____667 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____667 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____679 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____679 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___69_688  ->
    match uu___69_688 with
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
        let uu____690 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____690
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____693 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____693 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____704 =
          let uu____705 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____705 in
        let uu____708 =
          let uu____709 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____709 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____704 uu____708
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____728 =
          let uu____729 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____729 in
        let uu____732 =
          let uu____733 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____733 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____728 uu____732
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____743 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____743
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
    | uu____752 ->
        let uu____755 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____755 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____771 ->
        let uu____774 = quals_to_string quals in Prims.strcat uu____774 " "
let rec tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____833 = db_to_string x in Prims.strcat "Tm_bvar: " uu____833
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____835 = nm_to_string x in Prims.strcat "Tm_name: " uu____835
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____837 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____837
    | FStar_Syntax_Syntax.Tm_uinst uu____838 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____845 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____846 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____847 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____864 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____877 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____884 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____899 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____922 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____949 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____962 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____979,m) ->
        let uu____1021 = FStar_ST.op_Bang m in
        (match uu____1021 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1077 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1082,m) ->
        let uu____1088 = metadata_to_string m in
        Prims.strcat "Tm_meta:" uu____1088
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
and term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1090 =
      let uu____1091 = FStar_Options.ugly () in Prims.op_Negation uu____1091 in
    if uu____1090
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1097 = FStar_Options.print_implicits () in
         if uu____1097 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1099 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1124,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1160 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1190 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1208  ->
                                 match uu____1208 with
                                 | (t1,uu____1214) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1190
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1160 (FStar_String.concat "\\/") in
           let uu____1219 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1219
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1231 = tag_of_term t in
           let uu____1232 = sli m in
           let uu____1233 = term_to_string t' in
           let uu____1234 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1231 uu____1232
             uu____1233 uu____1234
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1247 = tag_of_term t in
           let uu____1248 = term_to_string t' in
           let uu____1249 = sli m0 in
           let uu____1250 = sli m1 in
           let uu____1251 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1247
             uu____1248 uu____1249 uu____1250 uu____1251
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1253,s,uu____1255)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1272 = FStar_Range.string_of_range r in
           let uu____1273 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1272
             uu____1273
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1280 = lid_to_string l in
           let uu____1281 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1282 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1280 uu____1281
             uu____1282
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1284) ->
           let uu____1289 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1289
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1291 = db_to_string x3 in
           let uu____1292 =
             let uu____1293 =
               let uu____1294 = tag_of_term x3.FStar_Syntax_Syntax.sort in
               Prims.strcat uu____1294 ")" in
             Prims.strcat ":(" uu____1293 in
           Prims.strcat uu____1291 uu____1292
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1298) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1325 = FStar_Options.print_universes () in
           if uu____1325
           then
             let uu____1326 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1326
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1346 = binders_to_string " -> " bs in
           let uu____1347 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1346 uu____1347
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1372 = binders_to_string " " bs in
                let uu____1373 = term_to_string t2 in
                let uu____1374 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1378 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1378) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1372 uu____1373
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1374
            | uu____1381 ->
                let uu____1384 = binders_to_string " " bs in
                let uu____1385 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1384 uu____1385)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1392 = bv_to_string xt in
           let uu____1393 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1396 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1392 uu____1393 uu____1396
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1421 = term_to_string t in
           let uu____1422 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1421 uu____1422
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1441 = lbs_to_string [] lbs in
           let uu____1442 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1441 uu____1442
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1503 =
                   let uu____1504 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1504
                     (FStar_Util.dflt "default") in
                 let uu____1509 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1503 uu____1509
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1525 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1525 in
           let uu____1526 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1526 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1565 = term_to_string head1 in
           let uu____1566 =
             let uu____1567 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1603  ->
                       match uu____1603 with
                       | (p,wopt,e) ->
                           let uu____1619 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1620 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1622 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1622 in
                           let uu____1623 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1619
                             uu____1620 uu____1623)) in
             FStar_Util.concat_l "\n\t|" uu____1567 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1565 uu____1566
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1630 = FStar_Options.print_universes () in
           if uu____1630
           then
             let uu____1631 = term_to_string t in
             let uu____1632 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1631 uu____1632
           else term_to_string t
       | uu____1634 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1636 =
      let uu____1637 = FStar_Options.ugly () in Prims.op_Negation uu____1637 in
    if uu____1636
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1659 = fv_to_string l in
           let uu____1660 =
             let uu____1661 =
               FStar_List.map
                 (fun uu____1672  ->
                    match uu____1672 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1661 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1659 uu____1660
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1684) ->
           let uu____1689 = FStar_Options.print_bound_var_types () in
           if uu____1689
           then
             let uu____1690 = bv_to_string x1 in
             let uu____1691 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1690 uu____1691
           else
             (let uu____1693 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1693)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1695 = FStar_Options.print_bound_var_types () in
           if uu____1695
           then
             let uu____1696 = bv_to_string x1 in
             let uu____1697 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1696 uu____1697
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1701 = FStar_Options.print_real_names () in
           if uu____1701
           then
             let uu____1702 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1702
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1714 = quals_to_string' quals in
      let uu____1715 =
        let uu____1716 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1731 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1732 =
                    let uu____1733 = FStar_Options.print_universes () in
                    if uu____1733
                    then
                      let uu____1734 =
                        let uu____1735 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1735 ">" in
                      Prims.strcat "<" uu____1734
                    else "" in
                  let uu____1737 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1738 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1731 uu____1732
                    uu____1737 uu____1738)) in
        FStar_Util.concat_l "\n and " uu____1716 in
      FStar_Util.format3 "%slet %s %s" uu____1714
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1715
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1745 = FStar_Options.print_effect_args () in
    if uu____1745
    then
      let uu____1746 = FStar_Syntax_Syntax.lcomp_comp lc in
      comp_to_string uu____1746
    else
      (let uu____1748 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1749 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1748 uu____1749)
and aqual_to_string: FStar_Syntax_Syntax.aqual -> Prims.string =
  fun uu___70_1750  ->
    match uu___70_1750 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1751 -> ""
and imp_to_string: Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string
  =
  fun s  ->
    fun aq  ->
      let uu____1754 = aqual_to_string aq in Prims.strcat uu____1754 s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1757 =
        let uu____1758 = FStar_Options.ugly () in
        Prims.op_Negation uu____1758 in
      if uu____1757
      then
        let uu____1759 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1759 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1765 = b in
         match uu____1765 with
         | (a,imp) ->
             let uu____1768 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1768
             then
               let uu____1769 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1769
             else
               (let uu____1771 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1773 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1773) in
                if uu____1771
                then
                  let uu____1774 = nm_to_string a in
                  imp_to_string uu____1774 imp
                else
                  (let uu____1776 =
                     let uu____1777 = nm_to_string a in
                     let uu____1778 =
                       let uu____1779 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1779 in
                     Prims.strcat uu____1777 uu____1778 in
                   imp_to_string uu____1776 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1785 = FStar_Options.print_implicits () in
        if uu____1785 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1787 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1787 (FStar_String.concat sep)
      else
        (let uu____1795 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1795 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___71_1802  ->
    match uu___71_1802 with
    | (a,imp) ->
        let uu____1809 = term_to_string a in imp_to_string uu____1809 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1812 = FStar_Options.print_implicits () in
      if uu____1812 then args else filter_imp args in
    let uu____1816 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1816 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1828 =
      let uu____1829 = FStar_Options.ugly () in Prims.op_Negation uu____1829 in
    if uu____1828
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1843 =
             let uu____1844 = FStar_Syntax_Subst.compress t in
             uu____1844.FStar_Syntax_Syntax.n in
           (match uu____1843 with
            | FStar_Syntax_Syntax.Tm_type uu____1847 when
                let uu____1848 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1848 -> term_to_string t
            | uu____1849 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1851 = univ_to_string u in
                     let uu____1852 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1851 uu____1852
                 | uu____1853 ->
                     let uu____1856 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1856))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1867 =
             let uu____1868 = FStar_Syntax_Subst.compress t in
             uu____1868.FStar_Syntax_Syntax.n in
           (match uu____1867 with
            | FStar_Syntax_Syntax.Tm_type uu____1871 when
                let uu____1872 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1872 -> term_to_string t
            | uu____1873 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1875 = univ_to_string u in
                     let uu____1876 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1875 uu____1876
                 | uu____1877 ->
                     let uu____1880 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1880))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1883 = FStar_Options.print_effect_args () in
             if uu____1883
             then
               let uu____1884 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1885 =
                 let uu____1886 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1886 (FStar_String.concat ", ") in
               let uu____1893 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1894 =
                 let uu____1895 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1895 (FStar_String.concat ", ") in
               let uu____1914 =
                 let uu____1915 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1915 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1884
                 uu____1885 uu____1893 uu____1894 uu____1914
             else
               (let uu____1925 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___72_1929  ->
                           match uu___72_1929 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1930 -> false)))
                    &&
                    (let uu____1932 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1932) in
                if uu____1925
                then
                  let uu____1933 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1933
                else
                  (let uu____1935 =
                     ((let uu____1938 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1938) &&
                        (let uu____1940 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1940))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____1935
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1942 =
                        (let uu____1945 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1945) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___73_1949  ->
                                   match uu___73_1949 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1950 -> false))) in
                      if uu____1942
                      then
                        let uu____1951 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1951
                      else
                        (let uu____1953 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1954 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1953 uu____1954)))) in
           let dec =
             let uu____1956 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___74_1966  ->
                       match uu___74_1966 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1972 =
                             let uu____1973 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1973 in
                           [uu____1972]
                       | uu____1974 -> [])) in
             FStar_All.pipe_right uu____1956 (FStar_String.concat " ") in
           FStar_Util.format2 "%s%s" basic dec)
and cflags_to_string: FStar_Syntax_Syntax.cflags -> Prims.string =
  fun c  ->
    match c with
    | FStar_Syntax_Syntax.TOTAL  -> "total"
    | FStar_Syntax_Syntax.MLEFFECT  -> "ml"
    | FStar_Syntax_Syntax.RETURN  -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN  -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL  -> "sometrivial"
    | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> "trivial_postcondition"
    | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> "should_not_inline"
    | FStar_Syntax_Syntax.LEMMA  -> "lemma"
    | FStar_Syntax_Syntax.CPS  -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____1978 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
and metadata_to_string: FStar_Syntax_Syntax.metadata -> Prims.string =
  fun uu___75_1984  ->
    match uu___75_1984 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____1997 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2027 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2045  ->
                              match uu____2045 with
                              | (t,uu____2051) -> term_to_string t)) in
                    FStar_All.pipe_right uu____2027
                      (FStar_String.concat "; "))) in
          FStar_All.pipe_right uu____1997 (FStar_String.concat "\\/") in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2057 = sli lid in
        FStar_Util.format1 "{Meta_named %s}" uu____2057
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2060) ->
        let uu____2061 = FStar_Range.string_of_range r in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2061
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2069 = sli m in
        let uu____2070 = term_to_string t in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2069 uu____2070
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2078 = sli m in
        let uu____2079 = sli m' in
        let uu____2080 = term_to_string t in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2078
          uu____2079 uu____2080
    | FStar_Syntax_Syntax.Meta_alien (uu____2081,s,t) ->
        let uu____2088 = term_to_string t in
        FStar_Util.format2 "{Meta_alien (%s, %s)}" s uu____2088
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2092 = b in
    match uu____2092 with
    | (a,imp) ->
        let n1 =
          let uu____2096 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2096
          then FStar_Util.JsonNull
          else
            (let uu____2098 =
               let uu____2099 = nm_to_string a in
               imp_to_string uu____2099 imp in
             FStar_Util.JsonStr uu____2098) in
        let t =
          let uu____2101 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2101 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2117 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2117
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2123 = FStar_Options.print_universes () in
    if uu____2123 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2128 =
      let uu____2129 = FStar_Options.ugly () in Prims.op_Negation uu____2129 in
    if uu____2128
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2133 = s in
       match uu____2133 with
       | (us,t) ->
           let uu____2140 =
             let uu____2141 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2141 in
           let uu____2142 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2140 uu____2142)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2146 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2147 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2148 =
      let uu____2149 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2149 in
    let uu____2150 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2151 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2146 uu____2147 uu____2148
      uu____2150 uu____2151
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
          let uu____2168 =
            let uu____2169 = FStar_Options.ugly () in
            Prims.op_Negation uu____2169 in
          if uu____2168
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2181 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2181 (FStar_String.concat ",\n\t") in
             let uu____2190 =
               let uu____2193 =
                 let uu____2196 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2197 =
                   let uu____2200 =
                     let uu____2201 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2201 in
                   let uu____2202 =
                     let uu____2205 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2206 =
                       let uu____2209 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2210 =
                         let uu____2213 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2214 =
                           let uu____2217 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2218 =
                             let uu____2221 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2222 =
                               let uu____2225 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2226 =
                                 let uu____2229 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2230 =
                                   let uu____2233 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2234 =
                                     let uu____2237 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2238 =
                                       let uu____2241 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2242 =
                                         let uu____2245 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2246 =
                                           let uu____2249 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2250 =
                                             let uu____2253 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2254 =
                                               let uu____2257 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2258 =
                                                 let uu____2261 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2262 =
                                                   let uu____2265 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2265] in
                                                 uu____2261 :: uu____2262 in
                                               uu____2257 :: uu____2258 in
                                             uu____2253 :: uu____2254 in
                                           uu____2249 :: uu____2250 in
                                         uu____2245 :: uu____2246 in
                                       uu____2241 :: uu____2242 in
                                     uu____2237 :: uu____2238 in
                                   uu____2233 :: uu____2234 in
                                 uu____2229 :: uu____2230 in
                               uu____2225 :: uu____2226 in
                             uu____2221 :: uu____2222 in
                           uu____2217 :: uu____2218 in
                         uu____2213 :: uu____2214 in
                       uu____2209 :: uu____2210 in
                     uu____2205 :: uu____2206 in
                   uu____2200 :: uu____2202 in
                 uu____2196 :: uu____2197 in
               (if for_free then "_for_free " else "") :: uu____2193 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2190)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let basic =
      match x.FStar_Syntax_Syntax.sigel with
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
          (lid,univs1,tps,k,uu____2283,uu____2284) ->
          let uu____2293 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
          let uu____2294 = binders_to_string " " tps in
          let uu____2295 = term_to_string k in
          FStar_Util.format4 "%stype %s %s : %s" uu____2293
            lid.FStar_Ident.str uu____2294 uu____2295
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____2299,uu____2300,uu____2301) ->
          let uu____2306 = FStar_Options.print_universes () in
          if uu____2306
          then
            let uu____2307 = univ_names_to_string univs1 in
            let uu____2308 = term_to_string t in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____2307
              lid.FStar_Ident.str uu____2308
          else
            (let uu____2310 = term_to_string t in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____2310)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____2314 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          (match uu____2314 with
           | (univs2,t1) ->
               let uu____2321 =
                 quals_to_string' x.FStar_Syntax_Syntax.sigquals in
               let uu____2322 =
                 let uu____2323 = FStar_Options.print_universes () in
                 if uu____2323
                 then
                   let uu____2324 = univ_names_to_string univs2 in
                   FStar_Util.format1 "<%s>" uu____2324
                 else "" in
               let uu____2326 = term_to_string t1 in
               FStar_Util.format4 "%sval %s %s : %s" uu____2321
                 lid.FStar_Ident.str uu____2322 uu____2326)
      | FStar_Syntax_Syntax.Sig_assume (lid,uu____2328,f) ->
          let uu____2330 = term_to_string f in
          FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2330
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____2332) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____2338 = term_to_string e in
          FStar_Util.format1 "let _ = %s" uu____2338
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2340) ->
          let uu____2349 = FStar_List.map sigelt_to_string ses in
          FStar_All.pipe_right uu____2349 (FStar_String.concat "\n")
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____2367) -> lift_wp
            | (uu____2374,FStar_Pervasives_Native.Some lift) -> lift in
          let uu____2382 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp) in
          (match uu____2382 with
           | (us,t) ->
               let uu____2393 = lid_to_string se.FStar_Syntax_Syntax.source in
               let uu____2394 = lid_to_string se.FStar_Syntax_Syntax.target in
               let uu____2395 = univ_names_to_string us in
               let uu____2396 = term_to_string t in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2393
                 uu____2394 uu____2395 uu____2396)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
          let uu____2406 = FStar_Options.print_universes () in
          if uu____2406
          then
            let uu____2407 =
              let uu____2412 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____2412 in
            (match uu____2407 with
             | (univs2,t) ->
                 let uu____2415 =
                   let uu____2428 =
                     let uu____2429 = FStar_Syntax_Subst.compress t in
                     uu____2429.FStar_Syntax_Syntax.n in
                   match uu____2428 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____2470 -> failwith "impossible" in
                 (match uu____2415 with
                  | (tps1,c1) ->
                      let uu____2501 = sli l in
                      let uu____2502 = univ_names_to_string univs2 in
                      let uu____2503 = binders_to_string " " tps1 in
                      let uu____2504 = comp_to_string c1 in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____2501
                        uu____2502 uu____2503 uu____2504))
          else
            (let uu____2506 = sli l in
             let uu____2507 = binders_to_string " " tps in
             let uu____2508 = comp_to_string c in
             FStar_Util.format3 "effect %s %s = %s" uu____2506 uu____2507
               uu____2508) in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____2509 ->
        let attrs =
          FStar_All.pipe_right x.FStar_Syntax_Syntax.sigattrs
            (FStar_List.map term_to_string) in
        let uu____2519 = FStar_All.pipe_right attrs (FStar_String.concat " ") in
        FStar_Util.format2 "[@%s]\n%s" uu____2519 basic
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2528 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2528 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2532,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2534;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2536;
                       FStar_Syntax_Syntax.lbdef = uu____2537;
                       FStar_Syntax_Syntax.lbattrs = uu____2538;_}::[]),uu____2539)
        ->
        let uu____2566 = lbname_to_string lb in
        let uu____2567 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2566 uu____2567
    | uu____2568 ->
        let uu____2569 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2569 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2583 = sli m.FStar_Syntax_Syntax.name in
    let uu____2584 =
      let uu____2585 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2585 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2583 uu____2584
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___76_2592  ->
    match uu___76_2592 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2595 = FStar_Util.string_of_int i in
        let uu____2596 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2595 uu____2596
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2599 = bv_to_string x in
        let uu____2600 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2599 uu____2600
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2607 = bv_to_string x in
        let uu____2608 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2607 uu____2608
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2611 = FStar_Util.string_of_int i in
        let uu____2612 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2611 uu____2612
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2615 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2615
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2619 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2619 (FStar_String.concat "; ")
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
           (let uu____2687 = f x in
            FStar_Util.string_builder_append strb uu____2687);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2694 = f x1 in
                 FStar_Util.string_builder_append strb uu____2694)) xs;
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
           (let uu____2727 = f x in
            FStar_Util.string_builder_append strb uu____2727);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2734 = f x1 in
                 FStar_Util.string_builder_append strb uu____2734)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)