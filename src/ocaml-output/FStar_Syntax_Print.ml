open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___69_3 ->
    match uu___69_3 with
    | FStar_Syntax_Syntax.Delta_constant -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____5 = FStar_Util.string_of_int i in
        Prims.strcat "Delta_defined_at_level " uu____5
    | FStar_Syntax_Syntax.Delta_equational -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____7 =
          let uu____8 = delta_depth_to_string d in Prims.strcat uu____8 ")" in
        Prims.strcat "Delta_abstract (" uu____7
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let uu____12 = FStar_Options.print_real_names () in
    if uu____12
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l -> sli l
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____23 =
      let uu____24 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____24 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____23
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____28 = FStar_Options.print_real_names () in
    if uu____28
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____33 =
      let uu____34 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____34 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____33
let (infix_prim_ops :
  (FStar_Ident.lident, Prims.string) FStar_Pervasives_Native.tuple2
    Prims.list)
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
let (unary_prim_ops :
  (FStar_Ident.lident, Prims.string) FStar_Pervasives_Native.tuple2
    Prims.list)
  =
  [(FStar_Parser_Const.op_Negation, "not");
  (FStar_Parser_Const.op_Minus, "-");
  (FStar_Parser_Const.not_lid, "~")]
let (is_prim_op :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun ps ->
    fun f ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____168 -> false
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____177 -> failwith "get_lid"
let (is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
let (is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
let (quants :
  (FStar_Ident.lident, Prims.string) FStar_Pervasives_Native.tuple2
    Prims.list)
  =
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")]
type exp = FStar_Syntax_Syntax.term[@@deriving show]
let (is_b2p : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t -> is_prim_op [FStar_Parser_Const.b2p_lid] t
let (is_quant : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t
let (is_ite : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t -> is_prim_op [FStar_Parser_Const.ite_lid] t
let (is_lex_cons : exp -> Prims.bool) =
  fun f -> is_prim_op [FStar_Parser_Const.lexcons_lid] f
let (is_lex_top : exp -> Prims.bool) =
  fun f -> is_prim_op [FStar_Parser_Const.lextop_lid] f
let is_inr :
  'Auu____232 'Auu____233 .
    ('Auu____232, 'Auu____233) FStar_Util.either -> Prims.bool
  =
  fun uu___70_241 ->
    match uu___70_241 with
    | FStar_Util.Inl uu____246 -> false
    | FStar_Util.Inr uu____247 -> true
let filter_imp :
  'Auu____250 .
    ('Auu____250,
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____250,
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___71_304 ->
            match uu___71_304 with
            | (uu____311, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____312)) -> false
            | uu____315 -> true))
let rec (reconstruct_lex :
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu____331 =
      let uu____332 = FStar_Syntax_Subst.compress e in
      uu____332.FStar_Syntax_Syntax.n in
    match uu____331 with
    | FStar_Syntax_Syntax.Tm_app (f, args) ->
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
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____458 ->
        let uu____459 = is_lex_top e in
        if uu____459
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f ->
    fun l ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____503 = f hd1 in if uu____503 then hd1 else find f tl1
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident, Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x ->
    fun xs ->
      let uu____523 =
        find
          (fun p -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____523
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____545 = get_lid e in find_lid uu____545 infix_prim_ops
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____553 = get_lid e in find_lid uu____553 unary_prim_ops
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t -> let uu____561 = get_lid t in find_lid uu____561 quants
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x -> FStar_Parser_Const.const_to_string x
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___72_567 ->
    match uu___72_567 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u ->
    let uu____573 = FStar_Options.hide_uvar_nums () in
    if uu____573
    then "?"
    else
      (let uu____575 =
         let uu____576 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____576 FStar_Util.string_of_int in
       Prims.strcat "?" uu____575)
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1 ->
    let uu____580 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____581 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____580 uu____581
let (univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string)
  =
  fun u ->
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
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,
        FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1 ->
    fun u ->
      let uu____608 = FStar_Syntax_Subst.compress_univ u in
      match uu____608 with
      | FStar_Syntax_Syntax.U_zero -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____618 -> (n1, (FStar_Pervasives_Native.Some u))
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u ->
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
       | FStar_Syntax_Syntax.U_zero -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____643 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____643 with
            | (n1, FStar_Pervasives_Native.None) ->
                FStar_Util.string_of_int n1
            | (n1, FStar_Pervasives_Native.Some u2) ->
                let uu____657 = univ_to_string u2 in
                let uu____658 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____657 uu____658)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____662 =
             let uu____663 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____663 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____662
       | FStar_Syntax_Syntax.U_unknown -> "unknown")
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us ->
    let uu____675 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____675 (FStar_String.concat ", ")
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us ->
    let uu____683 = FStar_List.map (fun x -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____683 (FStar_String.concat ", ")
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___73_692 ->
    match uu___73_692 with
    | FStar_Syntax_Syntax.Assumption -> "assume"
    | FStar_Syntax_Syntax.New -> "new"
    | FStar_Syntax_Syntax.Private -> "private"
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> "unfold"
    | FStar_Syntax_Syntax.Inline_for_extraction -> "inline"
    | FStar_Syntax_Syntax.NoExtract -> "noextract"
    | FStar_Syntax_Syntax.Visible_default -> "visible"
    | FStar_Syntax_Syntax.Irreducible -> "irreducible"
    | FStar_Syntax_Syntax.Abstract -> "abstract"
    | FStar_Syntax_Syntax.Noeq -> "noeq"
    | FStar_Syntax_Syntax.Unopteq -> "unopteq"
    | FStar_Syntax_Syntax.TotalEffect -> "total"
    | FStar_Syntax_Syntax.Discriminator l ->
        let uu____694 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____694
    | FStar_Syntax_Syntax.Projector (l, x) ->
        let uu____697 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____697 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns, fns) ->
        let uu____708 =
          let uu____709 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____709 in
        let uu____712 =
          let uu____713 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____713 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____708 uu____712
    | FStar_Syntax_Syntax.RecordConstructor (ns, fns) ->
        let uu____732 =
          let uu____733 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____733 in
        let uu____736 =
          let uu____737 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____737 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____732 uu____736
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____747 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____747
    | FStar_Syntax_Syntax.ExceptionConstructor -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect -> "Effect"
    | FStar_Syntax_Syntax.Reifiable -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str
    | FStar_Syntax_Syntax.OnlyName -> "OnlyName"
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu____756 ->
        let uu____759 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____759 (FStar_String.concat " ")
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu____775 ->
        let uu____778 = quals_to_string quals in Prims.strcat uu____778 " "
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.strcat "(" (Prims.strcat s ")")
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____848 = db_to_string x in Prims.strcat "Tm_bvar: " uu____848
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____850 = nm_to_string x in Prims.strcat "Tm_name: " uu____850
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____852 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____852
    | FStar_Syntax_Syntax.Tm_uinst uu____853 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____860 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____861 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted uu____862 -> "Tm_quoted"
    | FStar_Syntax_Syntax.Tm_abs uu____869 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____886 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____899 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____906 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____921 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____944 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____971 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____984 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1001, m) ->
        let uu____1043 = FStar_ST.op_Bang m in
        (match uu____1043 with
         | FStar_Pervasives_Native.None -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1153 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1158, m) ->
        let uu____1164 = metadata_to_string m in
        Prims.strcat "Tm_meta:" uu____1164
    | FStar_Syntax_Syntax.Tm_unknown -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1165 -> "Tm_lazy"
and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x ->
    let uu____1167 =
      let uu____1168 = FStar_Options.ugly () in Prims.op_Negation uu____1168 in
    if uu____1167
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1174 = FStar_Options.print_implicits () in
         if uu____1174 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1176 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1201, []) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1221 =
             let uu____1222 =
               let uu____1227 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
               FStar_Util.must uu____1227 in
             uu____1222 i.FStar_Syntax_Syntax.lkind i in
           term_to_string uu____1221
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
              FStar_Syntax_Syntax.antiquotes = uu____1276;_})
           ->
           let uu____1291 = term_to_string tm in
           FStar_Util.format1 "`(%s)" uu____1291
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
              FStar_Syntax_Syntax.antiquotes = uu____1293;_})
           ->
           let uu____1308 = term_to_string tm in
           FStar_Util.format1 "quote (%s)" uu____1308
       | FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1326 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args ->
                       let uu____1356 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1374 ->
                                 match uu____1374 with
                                 | (t1, uu____1380) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1356
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1326 (FStar_String.concat "\\/") in
           let uu____1385 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1385
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) ->
           let uu____1397 = tag_of_term t in
           let uu____1398 = sli m in
           let uu____1399 = term_to_string t' in
           let uu____1400 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1397 uu____1398
             uu____1399 uu____1400
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) ->
           let uu____1413 = tag_of_term t in
           let uu____1414 = term_to_string t' in
           let uu____1415 = sli m0 in
           let uu____1416 = sli m1 in
           let uu____1417 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1413
             uu____1414 uu____1415 uu____1416 uu____1417
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) ->
           let uu____1426 = FStar_Range.string_of_range r in
           let uu____1427 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1426
             uu____1427
       | FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1434 = lid_to_string l in
           let uu____1435 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1436 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1434 uu____1435
             uu____1436
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_desugared uu____1438) ->
           let uu____1443 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1443
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1445 = db_to_string x3 in
           let uu____1446 =
             let uu____1447 =
               let uu____1448 = tag_of_term x3.FStar_Syntax_Syntax.sort in
               Prims.strcat uu____1448 ")" in
             Prims.strcat ":(" uu____1447 in
           Prims.strcat uu____1445 uu____1446
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u, uu____1452) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1479 = FStar_Options.print_universes () in
           if uu____1479
           then
             let uu____1480 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1480
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
           let uu____1500 = binders_to_string " -> " bs in
           let uu____1501 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1500 uu____1501
       | FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1526 = binders_to_string " " bs in
                let uu____1527 = term_to_string t2 in
                let uu____1528 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1532 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1532) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1526 uu____1527
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1528
            | uu____1535 ->
                let uu____1538 = binders_to_string " " bs in
                let uu____1539 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1538 uu____1539)
       | FStar_Syntax_Syntax.Tm_refine (xt, f) ->
           let uu____1546 = bv_to_string xt in
           let uu____1547 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1550 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1546 uu____1547 uu____1550
       | FStar_Syntax_Syntax.Tm_app (t, args) ->
           let uu____1575 = term_to_string t in
           let uu____1576 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1575 uu____1576
       | FStar_Syntax_Syntax.Tm_let (lbs, e) ->
           let uu____1595 = lbs_to_string [] lbs in
           let uu____1596 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1595 uu____1596
       | FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1657 =
                   let uu____1658 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1658
                     (FStar_Util.dflt "default") in
                 let uu____1663 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1657 uu____1663
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1679 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1679 in
           let uu____1680 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1680 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1, branches) ->
           let uu____1719 = term_to_string head1 in
           let uu____1720 =
             let uu____1721 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1757 ->
                       match uu____1757 with
                       | (p, wopt, e) ->
                           let uu____1773 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1774 =
                             match wopt with
                             | FStar_Pervasives_Native.None -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1776 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1776 in
                           let uu____1777 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1773
                             uu____1774 uu____1777)) in
             FStar_Util.concat_l "\n\t|" uu____1721 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1719 uu____1720
       | FStar_Syntax_Syntax.Tm_uinst (t, us) ->
           let uu____1784 = FStar_Options.print_universes () in
           if uu____1784
           then
             let uu____1785 = term_to_string t in
             let uu____1786 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1785 uu____1786
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown -> "_")
and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x ->
    let uu____1789 =
      let uu____1790 = FStar_Options.ugly () in Prims.op_Negation uu____1790 in
    if uu____1789
    then
      let e =
        let uu____1792 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Syntax_Resugar.resugar_pat x uu____1792 in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l, pats) ->
           let uu____1815 = fv_to_string l in
           let uu____1816 =
             let uu____1817 =
               FStar_List.map
                 (fun uu____1828 ->
                    match uu____1828 with
                    | (x1, b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1817 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1815 uu____1816
       | FStar_Syntax_Syntax.Pat_dot_term (x1, uu____1840) ->
           let uu____1845 = FStar_Options.print_bound_var_types () in
           if uu____1845
           then
             let uu____1846 = bv_to_string x1 in
             let uu____1847 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1846 uu____1847
           else
             (let uu____1849 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1849)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1851 = FStar_Options.print_bound_var_types () in
           if uu____1851
           then
             let uu____1852 = bv_to_string x1 in
             let uu____1853 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1852 uu____1853
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1857 = FStar_Options.print_real_names () in
           if uu____1857
           then
             let uu____1858 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1858
           else "_")
and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool, FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals ->
    fun lbs ->
      let uu____1870 = quals_to_string' quals in
      let uu____1871 =
        let uu____1872 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb ->
                  let uu____1888 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs in
                  let uu____1889 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1890 =
                    let uu____1891 = FStar_Options.print_universes () in
                    if uu____1891
                    then
                      let uu____1892 =
                        let uu____1893 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1893 ">" in
                      Prims.strcat "<" uu____1892
                    else "" in
                  let uu____1895 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1896 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1888
                    uu____1889 uu____1890 uu____1895 uu____1896)) in
        FStar_Util.concat_l "\n and " uu____1872 in
      FStar_Util.format3 "%slet %s %s" uu____1870
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1871
and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___74_1902 ->
    match uu___74_1902 with
    | [] -> ""
    | tms ->
        let uu____1908 =
          let uu____1909 =
            FStar_List.map
              (fun t -> let uu____1915 = term_to_string t in paren uu____1915)
              tms in
          FStar_All.pipe_right uu____1909 (FStar_String.concat "; ") in
        FStar_Util.format1 "[@ %s]" uu____1908
and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc ->
    let uu____1919 = FStar_Options.print_effect_args () in
    if uu____1919
    then
      let uu____1920 = FStar_Syntax_Syntax.lcomp_comp lc in
      comp_to_string uu____1920
    else
      (let uu____1922 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1923 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1922 uu____1923)
and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___75_1924 ->
    match uu___75_1924 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false)) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) -> "$"
    | uu____1925 -> ""
and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s ->
    fun aq ->
      let uu____1928 = aqual_to_string aq in Prims.strcat uu____1928 s
and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow ->
    fun b ->
      let uu____1931 =
        let uu____1932 = FStar_Options.ugly () in
        Prims.op_Negation uu____1932 in
      if uu____1931
      then
        let uu____1933 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1933 with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1939 = b in
         match uu____1939 with
         | (a, imp) ->
             let uu____1942 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1942
             then
               let uu____1943 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1943
             else
               (let uu____1945 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1947 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1947) in
                if uu____1945
                then
                  let uu____1948 = nm_to_string a in
                  imp_to_string uu____1948 imp
                else
                  (let uu____1950 =
                     let uu____1951 = nm_to_string a in
                     let uu____1952 =
                       let uu____1953 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1953 in
                     Prims.strcat uu____1951 uu____1952 in
                   imp_to_string uu____1950 imp)))
and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b -> binder_to_string' false b
and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b -> binder_to_string' true b
and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep ->
    fun bs ->
      let bs1 =
        let uu____1959 = FStar_Options.print_implicits () in
        if uu____1959 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1961 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1961 (FStar_String.concat sep)
      else
        (let uu____1969 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1969 (FStar_String.concat sep))
and (arg_to_string :
  (FStar_Syntax_Syntax.term, FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___76_1976 ->
    match uu___76_1976 with
    | (a, imp) ->
        let uu____1983 = term_to_string a in imp_to_string uu____1983 imp
and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args ->
    let args1 =
      let uu____1986 = FStar_Options.print_implicits () in
      if uu____1986 then args else filter_imp args in
    let uu____1990 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1990 (FStar_String.concat " ")
and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let uu____2003 = FStar_Options.ugly () in
      if uu____2003
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c in
         let d = FStar_Parser_ToDocument.term_to_document e in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)
and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    let uu____2008 =
      let uu____2009 = FStar_Options.ugly () in Prims.op_Negation uu____2009 in
    if uu____2008
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t, uopt) ->
           let uu____2023 =
             let uu____2024 = FStar_Syntax_Subst.compress t in
             uu____2024.FStar_Syntax_Syntax.n in
           (match uu____2023 with
            | FStar_Syntax_Syntax.Tm_type uu____2027 when
                let uu____2028 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2028 -> term_to_string t
            | uu____2029 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2031 = univ_to_string u in
                     let uu____2032 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2031 uu____2032
                 | uu____2033 ->
                     let uu____2036 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2036))
       | FStar_Syntax_Syntax.GTotal (t, uopt) ->
           let uu____2047 =
             let uu____2048 = FStar_Syntax_Subst.compress t in
             uu____2048.FStar_Syntax_Syntax.n in
           (match uu____2047 with
            | FStar_Syntax_Syntax.Tm_type uu____2051 when
                let uu____2052 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2052 -> term_to_string t
            | uu____2053 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2055 = univ_to_string u in
                     let uu____2056 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2055 uu____2056
                 | uu____2057 ->
                     let uu____2060 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2060))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2063 = FStar_Options.print_effect_args () in
             if uu____2063
             then
               let uu____2064 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2065 =
                 let uu____2066 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2066 (FStar_String.concat ", ") in
               let uu____2073 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2074 =
                 let uu____2075 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2075 (FStar_String.concat ", ") in
               let uu____2094 =
                 let uu____2095 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2095 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2064
                 uu____2065 uu____2073 uu____2074 uu____2094
             else
               (let uu____2105 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___77_2109 ->
                           match uu___77_2109 with
                           | FStar_Syntax_Syntax.TOTAL -> true
                           | uu____2110 -> false)))
                    &&
                    (let uu____2112 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2112) in
                if uu____2105
                then
                  let uu____2113 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2113
                else
                  (let uu____2115 =
                     ((let uu____2118 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2118) &&
                        (let uu____2120 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2120))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2115
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2122 =
                        (let uu____2125 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2125) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___78_2129 ->
                                   match uu___78_2129 with
                                   | FStar_Syntax_Syntax.MLEFFECT -> true
                                   | uu____2130 -> false))) in
                      if uu____2122
                      then
                        let uu____2131 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2131
                      else
                        (let uu____2133 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2134 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2133 uu____2134)))) in
           let dec =
             let uu____2136 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___79_2146 ->
                       match uu___79_2146 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2152 =
                             let uu____2153 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2153 in
                           [uu____2152]
                       | uu____2154 -> [])) in
             FStar_All.pipe_right uu____2136 (FStar_String.concat " ") in
           FStar_Util.format2 "%s%s" basic dec)
and (cflags_to_string : FStar_Syntax_Syntax.cflags -> Prims.string) =
  fun c ->
    match c with
    | FStar_Syntax_Syntax.TOTAL -> "total"
    | FStar_Syntax_Syntax.MLEFFECT -> "ml"
    | FStar_Syntax_Syntax.RETURN -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL -> "sometrivial"
    | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION -> "trivial_postcondition"
    | FStar_Syntax_Syntax.SHOULD_NOT_INLINE -> "should_not_inline"
    | FStar_Syntax_Syntax.LEMMA -> "lemma"
    | FStar_Syntax_Syntax.CPS -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____2158 -> ""
and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi -> term_to_string phi
and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___80_2164 ->
    match uu___80_2164 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2177 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args ->
                    let uu____2207 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2225 ->
                              match uu____2225 with
                              | (t, uu____2231) -> term_to_string t)) in
                    FStar_All.pipe_right uu____2207
                      (FStar_String.concat "; "))) in
          FStar_All.pipe_right uu____2177 (FStar_String.concat "\\/") in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2237 = sli lid in
        FStar_Util.format1 "{Meta_named %s}" uu____2237
    | FStar_Syntax_Syntax.Meta_labeled (l, r, uu____2240) ->
        let uu____2241 = FStar_Range.string_of_range r in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2241
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____2249 = sli m in
        let uu____2250 = term_to_string t in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2249 uu____2250
    | FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) ->
        let uu____2258 = sli m in
        let uu____2259 = sli m' in
        let uu____2260 = term_to_string t in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2258
          uu____2259 uu____2260
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun x ->
      let uu____2267 = FStar_Options.ugly () in
      if uu____2267
      then term_to_string x
      else
        (let e = FStar_Syntax_Resugar.resugar_term' env x in
         let d = FStar_Parser_ToDocument.term_to_document e in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)
let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env ->
    fun b ->
      let uu____2277 = b in
      match uu____2277 with
      | (a, imp) ->
          let n1 =
            let uu____2281 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____2281
            then FStar_Util.JsonNull
            else
              (let uu____2283 =
                 let uu____2284 = nm_to_string a in
                 imp_to_string uu____2284 imp in
               FStar_Util.JsonStr uu____2283) in
          let t =
            let uu____2286 = term_to_string' env a.FStar_Syntax_Syntax.sort in
            FStar_Util.JsonStr uu____2286 in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env ->
    fun bs ->
      let uu____2305 = FStar_List.map (binder_to_json env) bs in
      FStar_Util.JsonList uu____2305
let (enclose_universes : Prims.string -> Prims.string) =
  fun s ->
    let uu____2311 = FStar_Options.print_universes () in
    if uu____2311 then Prims.strcat "<" (Prims.strcat s ">") else ""
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s ->
    let uu____2316 =
      let uu____2317 = FStar_Options.ugly () in Prims.op_Negation uu____2317 in
    if uu____2316
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2321 = s in
       match uu____2321 with
       | (us, t) ->
           let uu____2328 =
             let uu____2329 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2329 in
           let uu____2330 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2328 uu____2330)
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a ->
    let uu____2334 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2335 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2336 =
      let uu____2337 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2337 in
    let uu____2338 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2339 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2334 uu____2335 uu____2336
      uu____2338 uu____2339
let (eff_decl_to_string' :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string)
  =
  fun for_free ->
    fun r ->
      fun q ->
        fun ed ->
          let uu____2356 =
            let uu____2357 = FStar_Options.ugly () in
            Prims.op_Negation uu____2357 in
          if uu____2356
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2369 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2369 (FStar_String.concat ",\n\t") in
             let uu____2378 =
               let uu____2381 =
                 let uu____2384 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2385 =
                   let uu____2388 =
                     let uu____2389 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2389 in
                   let uu____2390 =
                     let uu____2393 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2394 =
                       let uu____2397 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2398 =
                         let uu____2401 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2402 =
                           let uu____2405 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2406 =
                             let uu____2409 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2410 =
                               let uu____2413 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2414 =
                                 let uu____2417 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2418 =
                                   let uu____2421 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2422 =
                                     let uu____2425 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2426 =
                                       let uu____2429 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2430 =
                                         let uu____2433 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2434 =
                                           let uu____2437 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2438 =
                                             let uu____2441 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2442 =
                                               let uu____2445 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2446 =
                                                 let uu____2449 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2450 =
                                                   let uu____2453 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2453] in
                                                 uu____2449 :: uu____2450 in
                                               uu____2445 :: uu____2446 in
                                             uu____2441 :: uu____2442 in
                                           uu____2437 :: uu____2438 in
                                         uu____2433 :: uu____2434 in
                                       uu____2429 :: uu____2430 in
                                     uu____2425 :: uu____2426 in
                                   uu____2421 :: uu____2422 in
                                 uu____2417 :: uu____2418 in
                               uu____2413 :: uu____2414 in
                             uu____2409 :: uu____2410 in
                           uu____2405 :: uu____2406 in
                         uu____2401 :: uu____2402 in
                       uu____2397 :: uu____2398 in
                     uu____2393 :: uu____2394 in
                   uu____2388 :: uu____2390 in
                 uu____2384 :: uu____2385 in
               (if for_free then "_for_free " else "") :: uu____2381 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2378)
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free ->
    fun ed -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    let uu____2464 =
      let uu____2465 = FStar_Options.ugly () in Prims.op_Negation uu____2465 in
    if uu____2464
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2471 -> ""
    else
      (let basic =
         match x.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff) ->
             "#light \"off\""
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
             (FStar_Pervasives_Native.None)) -> "#reset-options"
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
             (FStar_Pervasives_Native.Some s)) ->
             FStar_Util.format1 "#reset-options \"%s\"" s
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s)
             -> FStar_Util.format1 "#set-options \"%s\"" s
         | FStar_Syntax_Syntax.Sig_inductive_typ
             (lid, univs1, tps, k, uu____2482, uu____2483) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let binders_str = binders_to_string " " tps in
             let term_str = term_to_string k in
             let uu____2495 = FStar_Options.print_universes () in
             if uu____2495
             then
               let uu____2496 = univ_names_to_string univs1 in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2496 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid, univs1, t, uu____2501, uu____2502, uu____2503) ->
             let uu____2508 = FStar_Options.print_universes () in
             if uu____2508
             then
               let uu____2509 = univ_names_to_string univs1 in
               let uu____2510 = term_to_string t in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2509
                 lid.FStar_Ident.str uu____2510
             else
               (let uu____2512 = term_to_string t in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2512)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) ->
             let uu____2516 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let uu____2517 =
               let uu____2518 = FStar_Options.print_universes () in
               if uu____2518
               then
                 let uu____2519 = univ_names_to_string univs1 in
                 FStar_Util.format1 "<%s>" uu____2519
               else "" in
             let uu____2521 = term_to_string t in
             FStar_Util.format4 "%sval %s %s : %s" uu____2516
               lid.FStar_Ident.str uu____2517 uu____2521
         | FStar_Syntax_Syntax.Sig_assume (lid, uu____2523, f) ->
             let uu____2525 = term_to_string f in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2525
         | FStar_Syntax_Syntax.Sig_let (lbs, uu____2527) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2533 = term_to_string e in
             FStar_Util.format1 "let _ = %s" uu____2533
         | FStar_Syntax_Syntax.Sig_bundle (ses, uu____2535) ->
             let uu____2544 = FStar_List.map sigelt_to_string ses in
             FStar_All.pipe_right uu____2544 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
                   -> failwith "impossible"
               | (FStar_Pervasives_Native.Some lift_wp, uu____2562) ->
                   lift_wp
               | (uu____2569, FStar_Pervasives_Native.Some lift) -> lift in
             let uu____2577 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp) in
             (match uu____2577 with
              | (us, t) ->
                  let uu____2588 =
                    lid_to_string se.FStar_Syntax_Syntax.source in
                  let uu____2589 =
                    lid_to_string se.FStar_Syntax_Syntax.target in
                  let uu____2590 = univ_names_to_string us in
                  let uu____2591 = term_to_string t in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2588 uu____2589 uu____2590 uu____2591)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags1)
             ->
             let uu____2601 = FStar_Options.print_universes () in
             if uu____2601
             then
               let uu____2602 =
                 let uu____2607 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2607 in
               (match uu____2602 with
                | (univs2, t) ->
                    let uu____2610 =
                      let uu____2623 =
                        let uu____2624 = FStar_Syntax_Subst.compress t in
                        uu____2624.FStar_Syntax_Syntax.n in
                      match uu____2623 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> (bs, c1)
                      | uu____2665 -> failwith "impossible" in
                    (match uu____2610 with
                     | (tps1, c1) ->
                         let uu____2696 = sli l in
                         let uu____2697 = univ_names_to_string univs2 in
                         let uu____2698 = binders_to_string " " tps1 in
                         let uu____2699 = comp_to_string c1 in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2696 uu____2697 uu____2698 uu____2699))
             else
               (let uu____2701 = sli l in
                let uu____2702 = binders_to_string " " tps in
                let uu____2703 = comp_to_string c in
                FStar_Util.format3 "effect %s %s = %s" uu____2701 uu____2702
                  uu____2703)
         | FStar_Syntax_Syntax.Sig_splice t ->
             let uu____2705 = term_to_string t in
             FStar_Util.format1 "splice (%s)" uu____2705 in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2706 ->
           let uu____2709 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs in
           Prims.strcat uu____2709 (Prims.strcat "\n" basic))
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r ->
    fun msg ->
      let uu____2716 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2716 msg
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2720,
          { FStar_Syntax_Syntax.lbname = lb;
            FStar_Syntax_Syntax.lbunivs = uu____2722;
            FStar_Syntax_Syntax.lbtyp = t;
            FStar_Syntax_Syntax.lbeff = uu____2724;
            FStar_Syntax_Syntax.lbdef = uu____2725;
            FStar_Syntax_Syntax.lbattrs = uu____2726;
            FStar_Syntax_Syntax.lbpos = uu____2727;_}::[]),
         uu____2728)
        ->
        let uu____2755 = lbname_to_string lb in
        let uu____2756 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2755 uu____2756
    | uu____2757 ->
        let uu____2758 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2758 (FStar_String.concat ", ")
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m ->
    let uu____2772 = sli m.FStar_Syntax_Syntax.name in
    let uu____2773 =
      let uu____2774 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2774 (FStar_String.concat "\n") in
    let uu____2779 =
      let uu____2780 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports in
      FStar_All.pipe_right uu____2780 (FStar_String.concat "\n") in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2772 uu____2773 uu____2779
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___81_2787 ->
    match uu___81_2787 with
    | FStar_Syntax_Syntax.DB (i, x) ->
        let uu____2790 = FStar_Util.string_of_int i in
        let uu____2791 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2790 uu____2791
    | FStar_Syntax_Syntax.NM (x, i) ->
        let uu____2794 = bv_to_string x in
        let uu____2795 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2794 uu____2795
    | FStar_Syntax_Syntax.NT (x, t) ->
        let uu____2802 = bv_to_string x in
        let uu____2803 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2802 uu____2803
    | FStar_Syntax_Syntax.UN (i, u) ->
        let uu____2806 = FStar_Util.string_of_int i in
        let uu____2807 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2806 uu____2807
    | FStar_Syntax_Syntax.UD (u, i) ->
        let uu____2810 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2810
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s ->
    let uu____2814 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2814 (FStar_String.concat "; ")
let (abs_ascription_to_string :
  (FStar_Syntax_Syntax.lcomp, FStar_Ident.lident) FStar_Util.either
    FStar_Pervasives_Native.option -> Prims.string)
  =
  fun ascription ->
    let strb = FStar_Util.new_string_builder () in
    (match ascription with
     | FStar_Pervasives_Native.None ->
         FStar_Util.string_builder_append strb "None"
     | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          FStar_Util.string_builder_append strb
            (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)));
    FStar_Util.string_of_string_builder strb
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f ->
    fun elts ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "[";
           (let uu____2882 = f x in
            FStar_Util.string_builder_append strb uu____2882);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2889 = f x1 in
                 FStar_Util.string_builder_append strb uu____2889)) xs;
           FStar_Util.string_builder_append strb "]";
           FStar_Util.string_of_string_builder strb)
let set_to_string :
  'a . ('a -> Prims.string) -> 'a FStar_Util.set -> Prims.string =
  fun f ->
    fun s ->
      let elts = FStar_Util.set_elements s in
      match elts with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "{";
           (let uu____2922 = f x in
            FStar_Util.string_builder_append strb uu____2922);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2929 = f x1 in
                 FStar_Util.string_builder_append strb uu____2929)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep ->
    fun bvs ->
      let uu____2941 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs in
      binders_to_string sep uu____2941