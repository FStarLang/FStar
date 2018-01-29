open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___64_3  ->
    match uu___64_3 with
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
  fun uu___65_241  ->
    match uu___65_241 with
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
         (fun uu___66_304  ->
            match uu___66_304 with
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
  fun uu___67_567  ->
    match uu___67_567 with
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
  fun uu___68_696  ->
    match uu___68_696 with
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
        let uu____845 = db_to_string x in Prims.strcat "Tm_bvar: " uu____845
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____847 = nm_to_string x in Prims.strcat "Tm_name: " uu____847
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____849 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____849
    | FStar_Syntax_Syntax.Tm_uinst uu____850 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____857 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____858 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____859 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____876 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____889 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____896 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____911 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____934 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____961 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____974 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____991,m) ->
        let uu____1033 = FStar_ST.op_Bang m in
        (match uu____1033 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1089 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1094,m) ->
        let uu____1100 = metadata_to_string m in
        Prims.strcat "Tm_meta:" uu____1100
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
and term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1102 =
      let uu____1103 = FStar_Options.ugly () in Prims.op_Negation uu____1103 in
    if uu____1102
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed ((t,s),m) ->
           let uu____1158 = FStar_ST.op_Bang m in
           (match uu____1158 with
            | FStar_Pervasives_Native.Some t1 ->
                let uu____1217 = term_to_string t1 in
                FStar_Util.format1 "Memo_delayed(%s)" uu____1217
            | FStar_Pervasives_Native.None  ->
                let uu____1220 =
                  let uu____1221 = FStar_Options.print_implicits () in
                  if uu____1221
                  then
                    let uu____1222 =
                      FStar_List.map subst_to_string
                        (FStar_Pervasives_Native.fst s) in
                    FStar_All.pipe_right uu____1222
                      (FStar_String.concat "\n;;")
                  else "..." in
                let uu____1234 =
                  match FStar_Pervasives_Native.snd s with
                  | FStar_Pervasives_Native.None  -> "none"
                  | FStar_Pervasives_Native.Some r ->
                      let uu____1242 = FStar_Range.string_of_use_range r in
                      Prims.strcat "Some " uu____1242 in
                let uu____1243 = term_to_string t in
                FStar_Util.format3 "Tm_delayed([%s],%s)(%s)" uu____1220
                  uu____1234 uu____1243)
       | FStar_Syntax_Syntax.Tm_delayed uu____1244 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1269,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1305 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1335 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1353  ->
                                 match uu____1353 with
                                 | (t1,uu____1359) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1335
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1305 (FStar_String.concat "\\/") in
           let uu____1364 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1364
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1376 = tag_of_term t in
           let uu____1377 = sli m in
           let uu____1378 = term_to_string t' in
           let uu____1379 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1376 uu____1377
             uu____1378 uu____1379
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1392 = tag_of_term t in
           let uu____1393 = term_to_string t' in
           let uu____1394 = sli m0 in
           let uu____1395 = sli m1 in
           let uu____1396 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1392
             uu____1393 uu____1394 uu____1395 uu____1396
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1398,s,uu____1400)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1417 = FStar_Range.string_of_range r in
           let uu____1418 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1417
             uu____1418
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1425 = lid_to_string l in
           let uu____1426 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1427 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1425 uu____1426
             uu____1427
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1429) ->
           let uu____1434 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1434
       | FStar_Syntax_Syntax.Tm_bvar x1 ->
           let uu____1436 = db_to_string x1 in
           let uu____1437 =
             let uu____1438 =
               let uu____1439 = tag_of_term x1.FStar_Syntax_Syntax.sort in
               Prims.strcat uu____1439 ")" in
             Prims.strcat ":(" uu____1438 in
           Prims.strcat uu____1436 uu____1437
       | FStar_Syntax_Syntax.Tm_name x1 -> nm_to_string x1
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1443) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1470 = FStar_Options.print_universes () in
           if uu____1470
           then
             let uu____1471 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1471
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1491 = binders_to_string " -> " bs in
           let uu____1492 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1491 uu____1492
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1517 = binders_to_string " " bs in
                let uu____1518 = term_to_string t2 in
                let uu____1519 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1523 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1523) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1517 uu____1518
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1519
            | uu____1526 ->
                let uu____1529 = binders_to_string " " bs in
                let uu____1530 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1529 uu____1530)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1537 = bv_to_string xt in
           let uu____1538 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1541 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1537 uu____1538 uu____1541
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1566 = term_to_string t in
           let uu____1567 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1566 uu____1567
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1586 = lbs_to_string [] lbs in
           let uu____1587 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1586 uu____1587
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1648 =
                   let uu____1649 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1649
                     (FStar_Util.dflt "default") in
                 let uu____1654 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1648 uu____1654
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1670 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1670 in
           let uu____1671 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1671 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1710 = term_to_string head1 in
           let uu____1711 =
             let uu____1712 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1748  ->
                       match uu____1748 with
                       | (p,wopt,e) ->
                           let uu____1764 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1765 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1767 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1767 in
                           let uu____1768 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1764
                             uu____1765 uu____1768)) in
             FStar_Util.concat_l "\n\t|" uu____1712 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1710 uu____1711
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1775 = FStar_Options.print_universes () in
           if uu____1775
           then
             let uu____1776 = term_to_string t in
             let uu____1777 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1776 uu____1777
           else term_to_string t
       | uu____1779 -> tag_of_term x)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1781 =
      let uu____1782 = FStar_Options.ugly () in Prims.op_Negation uu____1782 in
    if uu____1781
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1804 = fv_to_string l in
           let uu____1805 =
             let uu____1806 =
               FStar_List.map
                 (fun uu____1817  ->
                    match uu____1817 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1806 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1804 uu____1805
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1829) ->
           let uu____1834 = FStar_Options.print_bound_var_types () in
           if uu____1834
           then
             let uu____1835 = bv_to_string x1 in
             let uu____1836 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1835 uu____1836
           else
             (let uu____1838 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1838)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1840 = FStar_Options.print_bound_var_types () in
           if uu____1840
           then
             let uu____1841 = bv_to_string x1 in
             let uu____1842 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1841 uu____1842
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1846 = FStar_Options.print_real_names () in
           if uu____1846
           then
             let uu____1847 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1847
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1859 = quals_to_string' quals in
      let uu____1860 =
        let uu____1861 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1876 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1877 =
                    let uu____1878 = FStar_Options.print_universes () in
                    if uu____1878
                    then
                      let uu____1879 =
                        let uu____1880 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1880 ">" in
                      Prims.strcat "<" uu____1879
                    else "" in
                  let uu____1882 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1883 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1876 uu____1877
                    uu____1882 uu____1883)) in
        FStar_Util.concat_l "\n and " uu____1861 in
      FStar_Util.format3 "%slet %s %s" uu____1859
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1860
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1890 = FStar_Options.print_effect_args () in
    if uu____1890
    then
      let uu____1891 = FStar_Syntax_Syntax.lcomp_comp lc in
      comp_to_string uu____1891
    else
      (let uu____1893 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1894 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1893 uu____1894)
and aqual_to_string: FStar_Syntax_Syntax.aqual -> Prims.string =
  fun uu___69_1895  ->
    match uu___69_1895 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1896 -> ""
and imp_to_string: Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string
  =
  fun s  ->
    fun aq  ->
      let uu____1899 = aqual_to_string aq in Prims.strcat uu____1899 s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1902 =
        let uu____1903 = FStar_Options.ugly () in
        Prims.op_Negation uu____1903 in
      if uu____1902
      then
        let uu____1904 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1904 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1910 = b in
         match uu____1910 with
         | (a,imp) ->
             let uu____1913 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1913
             then
               let uu____1914 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1914
             else
               (let uu____1916 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1918 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1918) in
                if uu____1916
                then
                  let uu____1919 = nm_to_string a in
                  imp_to_string uu____1919 imp
                else
                  (let uu____1921 =
                     let uu____1922 = nm_to_string a in
                     let uu____1923 =
                       let uu____1924 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1924 in
                     Prims.strcat uu____1922 uu____1923 in
                   imp_to_string uu____1921 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1930 = FStar_Options.print_implicits () in
        if uu____1930 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1932 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1932 (FStar_String.concat sep)
      else
        (let uu____1940 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1940 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___70_1947  ->
    match uu___70_1947 with
    | (a,imp) ->
        let uu____1954 = term_to_string a in imp_to_string uu____1954 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1957 = FStar_Options.print_implicits () in
      if uu____1957 then args else filter_imp args in
    let uu____1961 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1961 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1973 =
      let uu____1974 = FStar_Options.ugly () in Prims.op_Negation uu____1974 in
    if uu____1973
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1988 =
             let uu____1989 = FStar_Syntax_Subst.compress t in
             uu____1989.FStar_Syntax_Syntax.n in
           (match uu____1988 with
            | FStar_Syntax_Syntax.Tm_type uu____1992 when
                let uu____1993 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1993 -> term_to_string t
            | uu____1994 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1996 = univ_to_string u in
                     let uu____1997 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1996 uu____1997
                 | uu____1998 ->
                     let uu____2001 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2001))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2012 =
             let uu____2013 = FStar_Syntax_Subst.compress t in
             uu____2013.FStar_Syntax_Syntax.n in
           (match uu____2012 with
            | FStar_Syntax_Syntax.Tm_type uu____2016 when
                let uu____2017 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2017 -> term_to_string t
            | uu____2018 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2020 = univ_to_string u in
                     let uu____2021 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2020 uu____2021
                 | uu____2022 ->
                     let uu____2025 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2025))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2028 = FStar_Options.print_effect_args () in
             if uu____2028
             then
               let uu____2029 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2030 =
                 let uu____2031 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2031 (FStar_String.concat ", ") in
               let uu____2038 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2039 =
                 let uu____2040 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2040 (FStar_String.concat ", ") in
               let uu____2059 =
                 let uu____2060 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2060 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2029
                 uu____2030 uu____2038 uu____2039 uu____2059
             else
               (let uu____2070 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___71_2074  ->
                           match uu___71_2074 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2075 -> false)))
                    &&
                    (let uu____2077 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2077) in
                if uu____2070
                then
                  let uu____2078 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2078
                else
                  (let uu____2080 =
                     ((let uu____2083 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2083) &&
                        (let uu____2085 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2085))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2080
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2087 =
                        (let uu____2090 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2090) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___72_2094  ->
                                   match uu___72_2094 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2095 -> false))) in
                      if uu____2087
                      then
                        let uu____2096 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2096
                      else
                        (let uu____2098 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2099 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2098 uu____2099)))) in
           let dec =
             let uu____2101 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___73_2111  ->
                       match uu___73_2111 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2117 =
                             let uu____2118 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2118 in
                           [uu____2117]
                       | uu____2119 -> [])) in
             FStar_All.pipe_right uu____2101 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2123 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
and subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___74_2129  ->
    match uu___74_2129 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2132 = FStar_Util.string_of_int i in
        let uu____2133 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2132 uu____2133
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2136 = bv_to_string x in
        let uu____2137 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2136 uu____2137
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2144 = bv_to_string x in
        let uu____2145 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2144 uu____2145
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2148 = FStar_Util.string_of_int i in
        let uu____2149 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2148 uu____2149
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2152 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2152
and subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2154 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2154 (FStar_String.concat "; ")
and metadata_to_string: FStar_Syntax_Syntax.metadata -> Prims.string =
  fun uu___75_2161  ->
    match uu___75_2161 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2174 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2204 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2222  ->
                              match uu____2222 with
                              | (t,uu____2228) -> term_to_string t)) in
                    FStar_All.pipe_right uu____2204
                      (FStar_String.concat "; "))) in
          FStar_All.pipe_right uu____2174 (FStar_String.concat "\\/") in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2234 = sli lid in
        FStar_Util.format1 "{Meta_named %s}" uu____2234
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2237) ->
        let uu____2238 = FStar_Range.string_of_range r in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2238
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2246 = sli m in
        let uu____2247 = term_to_string t in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2246 uu____2247
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2255 = sli m in
        let uu____2256 = sli m' in
        let uu____2257 = term_to_string t in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2255
          uu____2256 uu____2257
    | FStar_Syntax_Syntax.Meta_alien (uu____2258,s,t) ->
        let uu____2265 = term_to_string t in
        FStar_Util.format2 "{Meta_alien (%s, %s)}" s uu____2265
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2269 = b in
    match uu____2269 with
    | (a,imp) ->
        let n1 =
          let uu____2273 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2273
          then FStar_Util.JsonNull
          else
            (let uu____2275 =
               let uu____2276 = nm_to_string a in
               imp_to_string uu____2276 imp in
             FStar_Util.JsonStr uu____2275) in
        let t =
          let uu____2278 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2278 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2294 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2294
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2300 = FStar_Options.print_universes () in
    if uu____2300 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2305 =
      let uu____2306 = FStar_Options.ugly () in Prims.op_Negation uu____2306 in
    if uu____2305
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2310 = s in
       match uu____2310 with
       | (us,t) ->
           let uu____2317 =
             let uu____2318 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2318 in
           let uu____2319 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2317 uu____2319)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2323 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2324 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2325 =
      let uu____2326 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2326 in
    let uu____2327 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2328 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2323 uu____2324 uu____2325
      uu____2327 uu____2328
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
          let uu____2345 =
            let uu____2346 = FStar_Options.ugly () in
            Prims.op_Negation uu____2346 in
          if uu____2345
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2358 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2358 (FStar_String.concat ",\n\t") in
             let uu____2367 =
               let uu____2370 =
                 let uu____2373 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2374 =
                   let uu____2377 =
                     let uu____2378 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2378 in
                   let uu____2379 =
                     let uu____2382 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2383 =
                       let uu____2386 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2387 =
                         let uu____2390 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2391 =
                           let uu____2394 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2395 =
                             let uu____2398 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2399 =
                               let uu____2402 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2403 =
                                 let uu____2406 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2407 =
                                   let uu____2410 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2411 =
                                     let uu____2414 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2415 =
                                       let uu____2418 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2419 =
                                         let uu____2422 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2423 =
                                           let uu____2426 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2427 =
                                             let uu____2430 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2431 =
                                               let uu____2434 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2435 =
                                                 let uu____2438 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2439 =
                                                   let uu____2442 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2442] in
                                                 uu____2438 :: uu____2439 in
                                               uu____2434 :: uu____2435 in
                                             uu____2430 :: uu____2431 in
                                           uu____2426 :: uu____2427 in
                                         uu____2422 :: uu____2423 in
                                       uu____2418 :: uu____2419 in
                                     uu____2414 :: uu____2415 in
                                   uu____2410 :: uu____2411 in
                                 uu____2406 :: uu____2407 in
                               uu____2402 :: uu____2403 in
                             uu____2398 :: uu____2399 in
                           uu____2394 :: uu____2395 in
                         uu____2390 :: uu____2391 in
                       uu____2386 :: uu____2387 in
                     uu____2382 :: uu____2383 in
                   uu____2377 :: uu____2379 in
                 uu____2373 :: uu____2374 in
               (if for_free then "_for_free " else "") :: uu____2370 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2367)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2453 =
      let uu____2454 = FStar_Options.ugly () in Prims.op_Negation uu____2454 in
    if uu____2453
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2460 -> ""
    else
      (let basic =
         match x.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
             "#light \"off\""
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
             (FStar_Pervasives_Native.None )) -> "#reset-options"
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
             (FStar_Pervasives_Native.Some s)) ->
             FStar_Util.format1 "#reset-options \"%s\"" s
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s)
             -> FStar_Util.format1 "#set-options \"%s\"" s
         | FStar_Syntax_Syntax.Sig_inductive_typ
             (lid,univs1,tps,k,uu____2471,uu____2472) ->
             let uu____2481 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let uu____2482 = binders_to_string " " tps in
             let uu____2483 = term_to_string k in
             FStar_Util.format4 "%stype %s %s : %s" uu____2481
               lid.FStar_Ident.str uu____2482 uu____2483
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2487,uu____2488,uu____2489) ->
             let uu____2494 = FStar_Options.print_universes () in
             if uu____2494
             then
               let uu____2495 = univ_names_to_string univs1 in
               let uu____2496 = term_to_string t in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2495
                 lid.FStar_Ident.str uu____2496
             else
               (let uu____2498 = term_to_string t in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2498)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2502 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2502 with
              | (univs2,t1) ->
                  let uu____2509 =
                    quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                  let uu____2510 =
                    let uu____2511 = FStar_Options.print_universes () in
                    if uu____2511
                    then
                      let uu____2512 = univ_names_to_string univs2 in
                      FStar_Util.format1 "<%s>" uu____2512
                    else "" in
                  let uu____2514 = term_to_string t1 in
                  FStar_Util.format4 "%sval %s %s : %s" uu____2509
                    lid.FStar_Ident.str uu____2510 uu____2514)
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2516,f) ->
             let uu____2518 = term_to_string f in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2518
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2520) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2526 = term_to_string e in
             FStar_Util.format1 "let _ = %s" uu____2526
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2528) ->
             let uu____2537 = FStar_List.map sigelt_to_string ses in
             FStar_All.pipe_right uu____2537 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None
                  ) -> failwith "impossible"
               | (FStar_Pervasives_Native.Some lift_wp,uu____2555) -> lift_wp
               | (uu____2562,FStar_Pervasives_Native.Some lift) -> lift in
             let uu____2570 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp) in
             (match uu____2570 with
              | (us,t) ->
                  let uu____2581 =
                    lid_to_string se.FStar_Syntax_Syntax.source in
                  let uu____2582 =
                    lid_to_string se.FStar_Syntax_Syntax.target in
                  let uu____2583 = univ_names_to_string us in
                  let uu____2584 = term_to_string t in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2581 uu____2582 uu____2583 uu____2584)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2594 = FStar_Options.print_universes () in
             if uu____2594
             then
               let uu____2595 =
                 let uu____2600 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2600 in
               (match uu____2595 with
                | (univs2,t) ->
                    let uu____2603 =
                      let uu____2616 =
                        let uu____2617 = FStar_Syntax_Subst.compress t in
                        uu____2617.FStar_Syntax_Syntax.n in
                      match uu____2616 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2658 -> failwith "impossible" in
                    (match uu____2603 with
                     | (tps1,c1) ->
                         let uu____2689 = sli l in
                         let uu____2690 = univ_names_to_string univs2 in
                         let uu____2691 = binders_to_string " " tps1 in
                         let uu____2692 = comp_to_string c1 in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2689 uu____2690 uu____2691 uu____2692))
             else
               (let uu____2694 = sli l in
                let uu____2695 = binders_to_string " " tps in
                let uu____2696 = comp_to_string c in
                FStar_Util.format3 "effect %s %s = %s" uu____2694 uu____2695
                  uu____2696) in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2697 ->
           let attrs =
             FStar_All.pipe_right x.FStar_Syntax_Syntax.sigattrs
               (FStar_List.map term_to_string) in
           let uu____2707 =
             FStar_All.pipe_right attrs (FStar_String.concat " ") in
           FStar_Util.format2 "[@%s]\n%s" uu____2707 basic)
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2716 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2716 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2720,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2722;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2724;
                       FStar_Syntax_Syntax.lbdef = uu____2725;_}::[]),uu____2726)
        ->
        let uu____2749 = lbname_to_string lb in
        let uu____2750 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2749 uu____2750
    | uu____2751 ->
        let uu____2752 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2752 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2766 = sli m.FStar_Syntax_Syntax.name in
    let uu____2767 =
      let uu____2768 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2768 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2766 uu____2767
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
           (let uu____2834 = f x in
            FStar_Util.string_builder_append strb uu____2834);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2841 = f x1 in
                 FStar_Util.string_builder_append strb uu____2841)) xs;
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
           (let uu____2874 = f x in
            FStar_Util.string_builder_append strb uu____2874);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2881 = f x1 in
                 FStar_Util.string_builder_append strb uu____2881)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)