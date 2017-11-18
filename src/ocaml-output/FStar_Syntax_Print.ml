open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___112_3  ->
    match uu___112_3 with
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
  fun uu___113_241  ->
    match uu___113_241 with
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
         (fun uu___114_304  ->
            match uu___114_304 with
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
  fun uu___115_567  ->
    match uu___115_567 with
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
    let uu____624 =
      let uu____625 = FStar_Options.ugly () in Prims.op_Negation uu____625 in
    if uu____624
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____629 = FStar_Syntax_Subst.compress_univ u in
       match uu____629 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____641 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____641
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____643 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____643 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____657 = univ_to_string u2 in
                let uu____658 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____657 uu____658)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____662 =
             let uu____663 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____663 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____662
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____675 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____675 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____687 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____687 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___116_696  ->
    match uu___116_696 with
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
        let uu____698 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____698
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____701 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____701 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____712 =
          let uu____713 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____713 in
        let uu____716 =
          let uu____717 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____717 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____712 uu____716
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____736 =
          let uu____737 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____737 in
        let uu____740 =
          let uu____741 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____741 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____736 uu____740
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____751 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____751
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
    | uu____760 ->
        let uu____763 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____763 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____779 ->
        let uu____782 = quals_to_string quals in Prims.strcat uu____782 " "
let rec tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____843 = db_to_string x in Prims.strcat "Tm_bvar: " uu____843
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____845 = nm_to_string x in Prims.strcat "Tm_name: " uu____845
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____847 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____847
    | FStar_Syntax_Syntax.Tm_uinst uu____848 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____855 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____856 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____857 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____874 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____887 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____894 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____909 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____932 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____959 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____972 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____989,m) ->
        let uu____1031 = FStar_ST.op_Bang m in
        (match uu____1031 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1106 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1111,m) ->
        let uu____1117 = metadata_to_string m in
        Prims.strcat "Tm_meta:" uu____1117
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
and term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1119 =
      let uu____1120 = FStar_Options.ugly () in Prims.op_Negation uu____1120 in
    if uu____1119
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1126 = FStar_Options.print_implicits () in
         if uu____1126 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1128 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1153,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1189 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1219 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1237  ->
                                 match uu____1237 with
                                 | (t1,uu____1243) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1219
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1189 (FStar_String.concat "\\/") in
           let uu____1248 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1248
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1260 = tag_of_term t in
           let uu____1261 = sli m in
           let uu____1262 = term_to_string t' in
           let uu____1263 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1260 uu____1261
             uu____1262 uu____1263
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1276 = tag_of_term t in
           let uu____1277 = term_to_string t' in
           let uu____1278 = sli m0 in
           let uu____1279 = sli m1 in
           let uu____1280 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1276
             uu____1277 uu____1278 uu____1279 uu____1280
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1282,s,uu____1284)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1301 = FStar_Range.string_of_range r in
           let uu____1302 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1301
             uu____1302
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1309 = lid_to_string l in
           let uu____1310 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1311 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1309 uu____1310
             uu____1311
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1313) ->
           let uu____1318 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1318
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1320 = db_to_string x3 in
           let uu____1321 =
             let uu____1322 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1322 in
           Prims.strcat uu____1320 uu____1321
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1326) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1353 = FStar_Options.print_universes () in
           if uu____1353
           then
             let uu____1354 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1354
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1374 = binders_to_string " -> " bs in
           let uu____1375 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1374 uu____1375
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1400 = binders_to_string " " bs in
                let uu____1401 = term_to_string t2 in
                let uu____1402 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1406 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1406) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1400 uu____1401
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1402
            | uu____1409 ->
                let uu____1412 = binders_to_string " " bs in
                let uu____1413 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1412 uu____1413)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1420 = bv_to_string xt in
           let uu____1421 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1424 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1420 uu____1421 uu____1424
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1449 = term_to_string t in
           let uu____1450 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1449 uu____1450
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1469 = lbs_to_string [] lbs in
           let uu____1470 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1469 uu____1470
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1531 =
                   let uu____1532 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1532
                     (FStar_Util.dflt "default") in
                 let uu____1537 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1531 uu____1537
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1553 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1553 in
           let uu____1554 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1554 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1593 = term_to_string head1 in
           let uu____1594 =
             let uu____1595 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1631  ->
                       match uu____1631 with
                       | (p,wopt,e) ->
                           let uu____1647 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1648 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1650 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1650 in
                           let uu____1651 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1647
                             uu____1648 uu____1651)) in
             FStar_Util.concat_l "\n\t|" uu____1595 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1593 uu____1594
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1658 = FStar_Options.print_universes () in
           if uu____1658
           then
             let uu____1659 = term_to_string t in
             let uu____1660 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1659 uu____1660
           else term_to_string t
       | uu____1662 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1664 =
      let uu____1665 = FStar_Options.ugly () in Prims.op_Negation uu____1665 in
    if uu____1664
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1687 = fv_to_string l in
           let uu____1688 =
             let uu____1689 =
               FStar_List.map
                 (fun uu____1700  ->
                    match uu____1700 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1689 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1687 uu____1688
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1712) ->
           let uu____1717 = FStar_Options.print_bound_var_types () in
           if uu____1717
           then
             let uu____1718 = bv_to_string x1 in
             let uu____1719 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1718 uu____1719
           else
             (let uu____1721 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1721)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1723 = FStar_Options.print_bound_var_types () in
           if uu____1723
           then
             let uu____1724 = bv_to_string x1 in
             let uu____1725 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1724 uu____1725
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1729 = FStar_Options.print_real_names () in
           if uu____1729
           then
             let uu____1730 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1730
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1742 = quals_to_string' quals in
      let uu____1743 =
        let uu____1744 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1759 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1760 =
                    let uu____1761 = FStar_Options.print_universes () in
                    if uu____1761
                    then
                      let uu____1762 =
                        let uu____1763 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1763 ">" in
                      Prims.strcat "<" uu____1762
                    else "" in
                  let uu____1765 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1766 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1759 uu____1760
                    uu____1765 uu____1766)) in
        FStar_Util.concat_l "\n and " uu____1744 in
      FStar_Util.format3 "%slet %s %s" uu____1742
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1743
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1773 = FStar_Options.print_effect_args () in
    if uu____1773
    then
      let uu____1774 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1774
    else
      (let uu____1776 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1777 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1776 uu____1777)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___117_1779  ->
      match uu___117_1779 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1782 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1787 =
        let uu____1788 = FStar_Options.ugly () in
        Prims.op_Negation uu____1788 in
      if uu____1787
      then
        let uu____1789 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1789 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1795 = b in
         match uu____1795 with
         | (a,imp) ->
             let uu____1798 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1798
             then
               let uu____1799 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1799
             else
               (let uu____1801 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1803 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1803) in
                if uu____1801
                then
                  let uu____1804 = nm_to_string a in
                  imp_to_string uu____1804 imp
                else
                  (let uu____1806 =
                     let uu____1807 = nm_to_string a in
                     let uu____1808 =
                       let uu____1809 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1809 in
                     Prims.strcat uu____1807 uu____1808 in
                   imp_to_string uu____1806 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1815 = FStar_Options.print_implicits () in
        if uu____1815 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1817 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1817 (FStar_String.concat sep)
      else
        (let uu____1825 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1825 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___118_1832  ->
    match uu___118_1832 with
    | (a,imp) ->
        let uu____1845 = term_to_string a in imp_to_string uu____1845 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1848 = FStar_Options.print_implicits () in
      if uu____1848 then args else filter_imp args in
    let uu____1852 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1852 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1866 =
      let uu____1867 = FStar_Options.ugly () in Prims.op_Negation uu____1867 in
    if uu____1866
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1881 =
             let uu____1882 = FStar_Syntax_Subst.compress t in
             uu____1882.FStar_Syntax_Syntax.n in
           (match uu____1881 with
            | FStar_Syntax_Syntax.Tm_type uu____1885 when
                let uu____1886 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1886 -> term_to_string t
            | uu____1887 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1889 = univ_to_string u in
                     let uu____1890 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1889 uu____1890
                 | uu____1891 ->
                     let uu____1894 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1894))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1905 =
             let uu____1906 = FStar_Syntax_Subst.compress t in
             uu____1906.FStar_Syntax_Syntax.n in
           (match uu____1905 with
            | FStar_Syntax_Syntax.Tm_type uu____1909 when
                let uu____1910 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1910 -> term_to_string t
            | uu____1911 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1913 = univ_to_string u in
                     let uu____1914 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1913 uu____1914
                 | uu____1915 ->
                     let uu____1918 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1918))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1921 = FStar_Options.print_effect_args () in
             if uu____1921
             then
               let uu____1922 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1923 =
                 let uu____1924 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1924 (FStar_String.concat ", ") in
               let uu____1931 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1932 =
                 let uu____1933 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1933 (FStar_String.concat ", ") in
               let uu____1954 =
                 let uu____1955 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1955 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1922
                 uu____1923 uu____1931 uu____1932 uu____1954
             else
               (let uu____1965 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___119_1969  ->
                           match uu___119_1969 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1970 -> false)))
                    &&
                    (let uu____1972 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1972) in
                if uu____1965
                then
                  let uu____1973 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1973
                else
                  (let uu____1975 =
                     ((let uu____1978 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1978) &&
                        (let uu____1980 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1980))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____1975
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1982 =
                        (let uu____1985 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1985) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___120_1989  ->
                                   match uu___120_1989 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1990 -> false))) in
                      if uu____1982
                      then
                        let uu____1991 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1991
                      else
                        (let uu____1993 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1994 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1993 uu____1994)))) in
           let dec =
             let uu____1996 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___121_2006  ->
                       match uu___121_2006 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2012 =
                             let uu____2013 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2013 in
                           [uu____2012]
                       | uu____2014 -> [])) in
             FStar_All.pipe_right uu____1996 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2018 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
and metadata_to_string: FStar_Syntax_Syntax.metadata -> Prims.string =
  fun uu___122_2024  ->
    match uu___122_2024 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2037 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2067 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2085  ->
                              match uu____2085 with
                              | (t,uu____2091) -> term_to_string t)) in
                    FStar_All.pipe_right uu____2067
                      (FStar_String.concat "; "))) in
          FStar_All.pipe_right uu____2037 (FStar_String.concat "\\/") in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2097 = sli lid in
        FStar_Util.format1 "{Meta_named %s}" uu____2097
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2100) ->
        let uu____2101 = FStar_Range.string_of_range r in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2101
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2109 = sli m in
        let uu____2110 = term_to_string t in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2109 uu____2110
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2118 = sli m in
        let uu____2119 = sli m' in
        let uu____2120 = term_to_string t in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2118
          uu____2119 uu____2120
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2124 = b in
    match uu____2124 with
    | (a,imp) ->
        let n1 =
          let uu____2128 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2128
          then FStar_Util.JsonNull
          else
            (let uu____2130 =
               let uu____2131 = nm_to_string a in
               imp_to_string uu____2131 imp in
             FStar_Util.JsonStr uu____2130) in
        let t =
          let uu____2133 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2133 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2149 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2149
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2155 = FStar_Options.print_universes () in
    if uu____2155 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2160 =
      let uu____2161 = FStar_Options.ugly () in Prims.op_Negation uu____2161 in
    if uu____2160
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2165 = s in
       match uu____2165 with
       | (us,t) ->
           let uu____2172 =
             let uu____2173 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2173 in
           let uu____2174 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2172 uu____2174)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2178 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2179 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2180 =
      let uu____2181 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2181 in
    let uu____2182 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2183 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2178 uu____2179 uu____2180
      uu____2182 uu____2183
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
          let uu____2200 =
            let uu____2201 = FStar_Options.ugly () in
            Prims.op_Negation uu____2201 in
          if uu____2200
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2213 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2213 (FStar_String.concat ",\n\t") in
             let uu____2222 =
               let uu____2225 =
                 let uu____2228 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2229 =
                   let uu____2232 =
                     let uu____2233 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2233 in
                   let uu____2234 =
                     let uu____2237 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2238 =
                       let uu____2241 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2242 =
                         let uu____2245 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2246 =
                           let uu____2249 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2250 =
                             let uu____2253 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2254 =
                               let uu____2257 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2258 =
                                 let uu____2261 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2262 =
                                   let uu____2265 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2266 =
                                     let uu____2269 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2270 =
                                       let uu____2273 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2274 =
                                         let uu____2277 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2278 =
                                           let uu____2281 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2282 =
                                             let uu____2285 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2286 =
                                               let uu____2289 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2290 =
                                                 let uu____2293 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2294 =
                                                   let uu____2297 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2297] in
                                                 uu____2293 :: uu____2294 in
                                               uu____2289 :: uu____2290 in
                                             uu____2285 :: uu____2286 in
                                           uu____2281 :: uu____2282 in
                                         uu____2277 :: uu____2278 in
                                       uu____2273 :: uu____2274 in
                                     uu____2269 :: uu____2270 in
                                   uu____2265 :: uu____2266 in
                                 uu____2261 :: uu____2262 in
                               uu____2257 :: uu____2258 in
                             uu____2253 :: uu____2254 in
                           uu____2249 :: uu____2250 in
                         uu____2245 :: uu____2246 in
                       uu____2241 :: uu____2242 in
                     uu____2237 :: uu____2238 in
                   uu____2232 :: uu____2234 in
                 uu____2228 :: uu____2229 in
               (if for_free then "_for_free " else "") :: uu____2225 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2222)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2308 =
      let uu____2309 = FStar_Options.ugly () in Prims.op_Negation uu____2309 in
    if uu____2308
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2315 -> ""
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
           (lid,univs1,tps,k,uu____2325,uu____2326) ->
           let uu____2335 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2336 = binders_to_string " " tps in
           let uu____2337 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2335
             lid.FStar_Ident.str uu____2336 uu____2337
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2341,uu____2342,uu____2343) ->
           let uu____2348 = FStar_Options.print_universes () in
           if uu____2348
           then
             let uu____2349 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2349 with
              | (univs2,t1) ->
                  let uu____2356 = univ_names_to_string univs2 in
                  let uu____2357 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2356
                    lid.FStar_Ident.str uu____2357)
           else
             (let uu____2359 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2359)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2363 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2363 with
            | (univs2,t1) ->
                let uu____2370 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2371 =
                  let uu____2372 = FStar_Options.print_universes () in
                  if uu____2372
                  then
                    let uu____2373 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2373
                  else "" in
                let uu____2375 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2370
                  lid.FStar_Ident.str uu____2371 uu____2375)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2377,f) ->
           let uu____2379 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2379
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2381) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2387 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2387
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2389) ->
           let uu____2398 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2398 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2416) -> lift_wp
             | (uu____2423,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2431 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2431 with
            | (us,t) ->
                let uu____2442 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2443 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2444 = univ_names_to_string us in
                let uu____2445 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2442
                  uu____2443 uu____2444 uu____2445)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2455 = FStar_Options.print_universes () in
           if uu____2455
           then
             let uu____2456 =
               let uu____2461 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2461 in
             (match uu____2456 with
              | (univs2,t) ->
                  let uu____2464 =
                    let uu____2477 =
                      let uu____2478 = FStar_Syntax_Subst.compress t in
                      uu____2478.FStar_Syntax_Syntax.n in
                    match uu____2477 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2519 -> failwith "impossible" in
                  (match uu____2464 with
                   | (tps1,c1) ->
                       let uu____2550 = sli l in
                       let uu____2551 = univ_names_to_string univs2 in
                       let uu____2552 = binders_to_string " " tps1 in
                       let uu____2553 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2550
                         uu____2551 uu____2552 uu____2553))
           else
             (let uu____2555 = sli l in
              let uu____2556 = binders_to_string " " tps in
              let uu____2557 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2555 uu____2556
                uu____2557))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2564 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2564 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2568,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2570;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2572;
                       FStar_Syntax_Syntax.lbdef = uu____2573;_}::[]),uu____2574)
        ->
        let uu____2597 = lbname_to_string lb in
        let uu____2598 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2597 uu____2598
    | uu____2599 ->
        let uu____2600 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2600 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2614 = sli m.FStar_Syntax_Syntax.name in
    let uu____2615 =
      let uu____2616 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2616 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2614 uu____2615
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___123_2623  ->
    match uu___123_2623 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2626 = FStar_Util.string_of_int i in
        let uu____2627 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2626 uu____2627
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2630 = bv_to_string x in
        let uu____2631 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2630 uu____2631
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2638 = bv_to_string x in
        let uu____2639 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2638 uu____2639
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2642 = FStar_Util.string_of_int i in
        let uu____2643 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2642 uu____2643
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2646 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2646
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2650 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2650 (FStar_String.concat "; ")
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
           (let uu____2718 = f x in
            FStar_Util.string_builder_append strb uu____2718);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2725 = f x1 in
                 FStar_Util.string_builder_append strb uu____2725)) xs;
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
           (let uu____2758 = f x in
            FStar_Util.string_builder_append strb uu____2758);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2765 = f x1 in
                 FStar_Util.string_builder_append strb uu____2765)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)