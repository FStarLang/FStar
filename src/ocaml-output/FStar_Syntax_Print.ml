open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___0_5 ->
    match uu___0_5 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____9 = FStar_Util.string_of_int i in
        Prims.op_Hat "Delta_constant_at_level " uu____9
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____14 = FStar_Util.string_of_int i in
        Prims.op_Hat "Delta_equational_at_level " uu____14
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____18 =
          let uu____20 = delta_depth_to_string d in Prims.op_Hat uu____20 ")" in
        Prims.op_Hat "Delta_abstract (" uu____18
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let uu____32 = FStar_Options.print_real_names () in
    if uu____32
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l -> sli l
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____59 =
      let uu____61 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.op_Hat "#" uu____61 in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____59
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____71 = FStar_Options.print_real_names () in
    if uu____71
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____84 =
      let uu____86 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.op_Hat "@" uu____86 in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____84
let (infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list) =
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
let (unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list) =
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
      | uu____308 -> false
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____321 -> failwith "get_lid"
let (is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
let (is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
let (quants : (FStar_Ident.lident * Prims.string) Prims.list) =
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")]
type exp = FStar_Syntax_Syntax.term
let (is_b2t : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t -> is_prim_op [FStar_Parser_Const.b2t_lid] t
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
  'Auu____424 'Auu____425 .
    ('Auu____424, 'Auu____425) FStar_Util.either -> Prims.bool
  =
  fun uu___1_435 ->
    match uu___1_435 with
    | FStar_Util.Inl uu____440 -> false
    | FStar_Util.Inr uu____442 -> true
let filter_imp :
  'Auu____449 .
    ('Auu____449 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____449 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___2_504 ->
            match uu___2_504 with
            | (uu____512, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____519, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____520)) -> false
            | (uu____525, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____526)) -> false
            | uu____532 -> true))
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e ->
    let uu____550 =
      let uu____551 = FStar_Syntax_Subst.compress e in
      uu____551.FStar_Syntax_Syntax.n in
    match uu____550 with
    | FStar_Syntax_Syntax.Tm_app (f, args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____612 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____612
        then
          let uu____621 =
            let uu____626 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____626 in
          (match uu____621 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____637 =
                 let uu____640 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____640 :: xs in
               FStar_Pervasives_Native.Some uu____637
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____652 ->
        let uu____653 = is_lex_top e in
        if uu____653
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f ->
    fun l ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____701 = f hd1 in if uu____701 then hd1 else find f tl1
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x ->
    fun xs ->
      let uu____733 =
        find
          (fun p -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____733
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____764 = get_lid e in find_lid uu____764 infix_prim_ops
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____776 = get_lid e in find_lid uu____776 unary_prim_ops
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t -> let uu____788 = get_lid t in find_lid uu____788 quants
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x -> FStar_Parser_Const.const_to_string x
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___3_802 ->
    match uu___3_802 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u ->
    let uu____813 = FStar_Options.hide_uvar_nums () in
    if uu____813
    then "?"
    else
      (let uu____820 =
         let uu____822 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____822 FStar_Util.string_of_int in
       Prims.op_Hat "?" uu____820)
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1 ->
    let uu____834 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____836 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____834 uu____836
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u ->
    let uu____862 = FStar_Options.hide_uvar_nums () in
    if uu____862
    then "?"
    else
      (let uu____869 =
         let uu____871 =
           let uu____873 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____873 FStar_Util.string_of_int in
         let uu____877 =
           let uu____879 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.op_Hat ":" uu____879 in
         Prims.op_Hat uu____871 uu____877 in
       Prims.op_Hat "?" uu____869)
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1 ->
    fun u ->
      let uu____907 = FStar_Syntax_Subst.compress_univ u in
      match uu____907 with
      | FStar_Syntax_Syntax.U_zero -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____920 -> (n1, (FStar_Pervasives_Native.Some u))
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u ->
    let uu____931 = FStar_Syntax_Subst.compress_univ u in
    match uu____931 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____942 = univ_uvar_to_string u1 in
        Prims.op_Hat "U_unif " uu____942
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____949 = FStar_Util.string_of_int x in
        Prims.op_Hat "@" uu____949
    | FStar_Syntax_Syntax.U_zero -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____954 = int_of_univ (Prims.parse_int "1") u1 in
        (match uu____954 with
         | (n1, FStar_Pervasives_Native.None) -> FStar_Util.string_of_int n1
         | (n1, FStar_Pervasives_Native.Some u2) ->
             let uu____975 = univ_to_string u2 in
             let uu____977 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "(%s + %s)" uu____975 uu____977)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____983 =
          let uu____985 = FStar_List.map univ_to_string us in
          FStar_All.pipe_right uu____985 (FStar_String.concat ", ") in
        FStar_Util.format1 "(max %s)" uu____983
    | FStar_Syntax_Syntax.U_unknown -> "unknown"
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us ->
    let uu____1004 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____1004 (FStar_String.concat ", ")
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us ->
    let uu____1021 = FStar_List.map (fun x -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1021 (FStar_String.concat ", ")
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___4_1039 ->
    match uu___4_1039 with
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
    | FStar_Syntax_Syntax.Logic -> "logic"
    | FStar_Syntax_Syntax.TotalEffect -> "total"
    | FStar_Syntax_Syntax.Discriminator l ->
        let uu____1055 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1055
    | FStar_Syntax_Syntax.Projector (l, x) ->
        let uu____1060 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1060
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns, fns) ->
        let uu____1073 =
          let uu____1075 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1075 in
        let uu____1076 =
          let uu____1078 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1078 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1073 uu____1076
    | FStar_Syntax_Syntax.RecordConstructor (ns, fns) ->
        let uu____1104 =
          let uu____1106 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1106 in
        let uu____1107 =
          let uu____1109 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1109 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1104 uu____1107
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1126 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1126
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
    | uu____1149 ->
        let uu____1152 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1152 (FStar_String.concat " ")
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu____1180 ->
        let uu____1183 = quals_to_string quals in Prims.op_Hat uu____1183 " "
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.op_Hat "(" (Prims.op_Hat s ")")
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1379 = db_to_string x in
        Prims.op_Hat "Tm_bvar: " uu____1379
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1383 = nm_to_string x in
        Prims.op_Hat "Tm_name: " uu____1383
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1387 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.op_Hat "Tm_fvar: " uu____1387
    | FStar_Syntax_Syntax.Tm_uinst uu____1390 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1398 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1400 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1402,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
           FStar_Syntax_Syntax.antiquotes = uu____1403;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1417,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
           FStar_Syntax_Syntax.antiquotes = uu____1418;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1432 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1452 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1468 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1476 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1494 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1518 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1546 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1561 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1575, m) ->
        let uu____1613 = FStar_ST.op_Bang m in
        (match uu____1613 with
         | FStar_Pervasives_Native.None -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1649 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1655, m) ->
        let uu____1661 = metadata_to_string m in
        Prims.op_Hat "Tm_meta:" uu____1661
    | FStar_Syntax_Syntax.Tm_unknown -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1665 -> "Tm_lazy"
and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x ->
    let uu____1668 =
      let uu____1670 = FStar_Options.ugly () in Prims.op_Negation uu____1670 in
    if uu____1668
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1684 = FStar_Options.print_implicits () in
         if uu____1684 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1692 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1717, []) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1743, thunk1);
             FStar_Syntax_Syntax.ltyp = uu____1745;
             FStar_Syntax_Syntax.rng = uu____1746;_}
           ->
           let uu____1757 =
             let uu____1759 =
               let uu____1761 = FStar_Common.force_thunk thunk1 in
               term_to_string uu____1761 in
             Prims.op_Hat uu____1759 "]" in
           Prims.op_Hat "[LAZYEMB:" uu____1757
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1767 =
             let uu____1769 =
               let uu____1771 =
                 let uu____1772 =
                   let uu____1781 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
                   FStar_Util.must uu____1781 in
                 uu____1772 i.FStar_Syntax_Syntax.lkind i in
               term_to_string uu____1771 in
             Prims.op_Hat uu____1769 "]" in
           Prims.op_Hat "[lazy:" uu____1767
       | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static ->
                let print_aq uu____1850 =
                  match uu____1850 with
                  | (bv, t) ->
                      let uu____1858 = bv_to_string bv in
                      let uu____1860 = term_to_string t in
                      FStar_Util.format2 "%s -> %s" uu____1858 uu____1860 in
                let uu____1863 = term_to_string tm in
                let uu____1865 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes in
                FStar_Util.format2 "`(%s)%s" uu____1863 uu____1865
            | FStar_Syntax_Syntax.Quote_dynamic ->
                let uu____1874 = term_to_string tm in
                FStar_Util.format1 "quote (%s)" uu____1874)
       | FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1897 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args ->
                       let uu____1934 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1959 ->
                                 match uu____1959 with
                                 | (t1, uu____1968) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1934
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1897 (FStar_String.concat "\\/") in
           let uu____1983 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1983
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) ->
           let uu____1997 = tag_of_term t in
           let uu____1999 = sli m in
           let uu____2001 = term_to_string t' in
           let uu____2003 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1997 uu____1999
             uu____2001 uu____2003
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) ->
           let uu____2018 = tag_of_term t in
           let uu____2020 = term_to_string t' in
           let uu____2022 = sli m0 in
           let uu____2024 = sli m1 in
           let uu____2026 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2018
             uu____2020 uu____2022 uu____2024 uu____2026
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) ->
           let uu____2041 = FStar_Range.string_of_range r in
           let uu____2043 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2041
             uu____2043
       | FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2052 = lid_to_string l in
           let uu____2054 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____2056 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2052 uu____2054
             uu____2056
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_desugared uu____2060) ->
           let uu____2065 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2065
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2069 = db_to_string x3 in
           let uu____2071 =
             let uu____2073 =
               let uu____2075 = tag_of_term x3.FStar_Syntax_Syntax.sort in
               Prims.op_Hat uu____2075 ")" in
             Prims.op_Hat ":(" uu____2073 in
           Prims.op_Hat uu____2069 uu____2071
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u, ([], uu____2082)) ->
           let uu____2097 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ()) in
           if uu____2097
           then ctx_uvar_to_string u
           else
             (let uu____2103 =
                let uu____2105 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2105 in
              Prims.op_Hat "?" uu____2103)
       | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
           let uu____2128 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ()) in
           if uu____2128
           then
             let uu____2132 = ctx_uvar_to_string u in
             let uu____2134 =
               let uu____2136 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s) in
               FStar_All.pipe_right uu____2136 (FStar_String.concat "; ") in
             FStar_Util.format2 "(%s @ %s)" uu____2132 uu____2134
           else
             (let uu____2155 =
                let uu____2157 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2157 in
              Prims.op_Hat "?" uu____2155)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2164 = FStar_Options.print_universes () in
           if uu____2164
           then
             let uu____2168 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____2168
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
           let uu____2196 = binders_to_string " -> " bs in
           let uu____2199 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____2196 uu____2199
       | FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2231 = binders_to_string " " bs in
                let uu____2234 = term_to_string t2 in
                let uu____2236 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2245 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____2245) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2231 uu____2234
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____2236
            | uu____2249 ->
                let uu____2252 = binders_to_string " " bs in
                let uu____2255 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____2252 uu____2255)
       | FStar_Syntax_Syntax.Tm_refine (xt, f) ->
           let uu____2264 = bv_to_string xt in
           let uu____2266 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____2269 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____2264 uu____2266 uu____2269
       | FStar_Syntax_Syntax.Tm_app (t, args) ->
           let uu____2301 = term_to_string t in
           let uu____2303 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____2301 uu____2303
       | FStar_Syntax_Syntax.Tm_let (lbs, e) ->
           let uu____2326 = lbs_to_string [] lbs in
           let uu____2328 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____2326 uu____2328
       | FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2393 =
                   let uu____2395 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____2395
                     (FStar_Util.dflt "default") in
                 let uu____2406 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____2393 uu____2406
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2427 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____2427 in
           let uu____2430 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2430 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1, branches) ->
           let uu____2471 = term_to_string head1 in
           let uu____2473 =
             let uu____2475 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____2508 ->
                       match uu____2508 with
                       | (p, wopt, e) ->
                           let uu____2525 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____2528 =
                             match wopt with
                             | FStar_Pervasives_Native.None -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____2533 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____2533 in
                           let uu____2537 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____2525
                             uu____2528 uu____2537)) in
             FStar_Util.concat_l "\n\t|" uu____2475 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2471 uu____2473
       | FStar_Syntax_Syntax.Tm_uinst (t, us) ->
           let uu____2549 = FStar_Options.print_universes () in
           if uu____2549
           then
             let uu____2553 = term_to_string t in
             let uu____2555 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____2553 uu____2555
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown -> "_")
and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar ->
    let uu____2562 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders in
    let uu____2565 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
    let uu____2567 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2562 uu____2565
      uu____2567
and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2570 ->
    match uu___5_2570 with
    | FStar_Syntax_Syntax.DB (i, x) ->
        let uu____2576 = FStar_Util.string_of_int i in
        let uu____2578 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2576 uu____2578
    | FStar_Syntax_Syntax.NM (x, i) ->
        let uu____2585 = bv_to_string x in
        let uu____2587 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2585 uu____2587
    | FStar_Syntax_Syntax.NT (x, t) ->
        let uu____2596 = bv_to_string x in
        let uu____2598 = term_to_string t in
        FStar_Util.format2 "NT (%s, %s)" uu____2596 uu____2598
    | FStar_Syntax_Syntax.UN (i, u) ->
        let uu____2605 = FStar_Util.string_of_int i in
        let uu____2607 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2605 uu____2607
    | FStar_Syntax_Syntax.UD (u, i) ->
        let uu____2614 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2614
and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s ->
    let uu____2618 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2618 (FStar_String.concat "; ")
and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x ->
    let uu____2634 =
      let uu____2636 = FStar_Options.ugly () in Prims.op_Negation uu____2636 in
    if uu____2634
    then
      let e =
        let uu____2641 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Syntax_Resugar.resugar_pat x uu____2641 in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l, pats) ->
           let uu____2670 = fv_to_string l in
           let uu____2672 =
             let uu____2674 =
               FStar_List.map
                 (fun uu____2688 ->
                    match uu____2688 with
                    | (x1, b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.op_Hat "#" p else p) pats in
             FStar_All.pipe_right uu____2674 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____2670 uu____2672
       | FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2713) ->
           let uu____2718 = FStar_Options.print_bound_var_types () in
           if uu____2718
           then
             let uu____2722 = bv_to_string x1 in
             let uu____2724 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____2722 uu____2724
           else
             (let uu____2729 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____2729)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2733 = FStar_Options.print_bound_var_types () in
           if uu____2733
           then
             let uu____2737 = bv_to_string x1 in
             let uu____2739 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____2737 uu____2739
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2746 = FStar_Options.print_bound_var_types () in
           if uu____2746
           then
             let uu____2750 = bv_to_string x1 in
             let uu____2752 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "_wild_%s:%s" uu____2750 uu____2752
           else bv_to_string x1)
and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals ->
    fun lbs ->
      let uu____2761 = quals_to_string' quals in
      let uu____2763 =
        let uu____2765 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb ->
                  let uu____2785 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs in
                  let uu____2787 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____2789 =
                    let uu____2791 = FStar_Options.print_universes () in
                    if uu____2791
                    then
                      let uu____2795 =
                        let uu____2797 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.op_Hat uu____2797 ">" in
                      Prims.op_Hat "<" uu____2795
                    else "" in
                  let uu____2804 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____2806 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2785
                    uu____2787 uu____2789 uu____2804 uu____2806)) in
        FStar_Util.concat_l "\n and " uu____2765 in
      FStar_Util.format3 "%slet %s %s" uu____2761
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2763
and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2821 ->
    match uu___6_2821 with
    | [] -> ""
    | tms ->
        let uu____2829 =
          let uu____2831 =
            FStar_List.map
              (fun t -> let uu____2839 = term_to_string t in paren uu____2839)
              tms in
          FStar_All.pipe_right uu____2831 (FStar_String.concat "; ") in
        FStar_Util.format1 "[@ %s]" uu____2829
and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc ->
    let uu____2848 = FStar_Options.print_effect_args () in
    if uu____2848
    then
      let uu____2852 = FStar_Syntax_Syntax.lcomp_comp lc in
      comp_to_string uu____2852
    else
      (let uu____2855 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____2857 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____2855 uu____2857)
and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s ->
    fun uu___7_2861 ->
      match uu___7_2861 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false))
          -> Prims.op_Hat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) ->
          Prims.op_Hat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
          Prims.op_Hat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.op_Hat "[|" (Prims.op_Hat s "|]")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____2879 =
            let uu____2881 = term_to_string t in
            Prims.op_Hat uu____2881 (Prims.op_Hat "]" s) in
          Prims.op_Hat "#[" uu____2879
      | FStar_Pervasives_Native.None -> s
and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq -> aqual_to_string' "" aq
and (imp_to_string :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  = fun s -> fun aq -> aqual_to_string' s aq
and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun is_arrow ->
    fun b ->
      let uu____2901 =
        let uu____2903 = FStar_Options.ugly () in
        Prims.op_Negation uu____2903 in
      if uu____2901
      then
        let uu____2907 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____2907 with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2918 = b in
         match uu____2918 with
         | (a, imp) ->
             let uu____2932 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____2932
             then
               let uu____2936 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.op_Hat "_:" uu____2936
             else
               (let uu____2941 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2944 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____2944) in
                if uu____2941
                then
                  let uu____2948 = nm_to_string a in
                  imp_to_string uu____2948 imp
                else
                  (let uu____2952 =
                     let uu____2954 = nm_to_string a in
                     let uu____2956 =
                       let uu____2958 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.op_Hat ":" uu____2958 in
                     Prims.op_Hat uu____2954 uu____2956 in
                   imp_to_string uu____2952 imp)))
and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b -> binder_to_string' false b
and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  = fun b -> binder_to_string' true b
and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep ->
    fun bs ->
      let bs1 =
        let uu____2977 = FStar_Options.print_implicits () in
        if uu____2977 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____2988 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____2988 (FStar_String.concat sep)
      else
        (let uu____3016 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____3016 (FStar_String.concat sep))
and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_3030 ->
    match uu___8_3030 with
    | (a, imp) ->
        let uu____3044 = term_to_string a in imp_to_string uu____3044 imp
and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args ->
    let args1 =
      let uu____3056 = FStar_Options.print_implicits () in
      if uu____3056 then args else filter_imp args in
    let uu____3071 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____3071 (FStar_String.concat " ")
and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let uu____3100 = FStar_Options.ugly () in
      if uu____3100
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c in
         let d = FStar_Parser_ToDocument.term_to_document e in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)
and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    let uu____3111 =
      let uu____3113 = FStar_Options.ugly () in Prims.op_Negation uu____3113 in
    if uu____3111
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t, uopt) ->
           let uu____3134 =
             let uu____3135 = FStar_Syntax_Subst.compress t in
             uu____3135.FStar_Syntax_Syntax.n in
           (match uu____3134 with
            | FStar_Syntax_Syntax.Tm_type uu____3139 when
                let uu____3140 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____3140 -> term_to_string t
            | uu____3142 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3145 = univ_to_string u in
                     let uu____3147 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____3145 uu____3147
                 | uu____3150 ->
                     let uu____3153 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____3153))
       | FStar_Syntax_Syntax.GTotal (t, uopt) ->
           let uu____3166 =
             let uu____3167 = FStar_Syntax_Subst.compress t in
             uu____3167.FStar_Syntax_Syntax.n in
           (match uu____3166 with
            | FStar_Syntax_Syntax.Tm_type uu____3171 when
                let uu____3172 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____3172 -> term_to_string t
            | uu____3174 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3177 = univ_to_string u in
                     let uu____3179 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____3177 uu____3179
                 | uu____3182 ->
                     let uu____3185 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____3185))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3191 = FStar_Options.print_effect_args () in
             if uu____3191
             then
               let uu____3195 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____3197 =
                 let uu____3199 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____3199 (FStar_String.concat ", ") in
               let uu____3214 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____3216 =
                 let uu____3218 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____3218 (FStar_String.concat ", ") in
               let uu____3245 = cflags_to_string c1.FStar_Syntax_Syntax.flags in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3195
                 uu____3197 uu____3214 uu____3216 uu____3245
             else
               (let uu____3250 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3256 ->
                           match uu___9_3256 with
                           | FStar_Syntax_Syntax.TOTAL -> true
                           | uu____3259 -> false)))
                    &&
                    (let uu____3262 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____3262) in
                if uu____3250
                then
                  let uu____3266 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____3266
                else
                  (let uu____3271 =
                     ((let uu____3275 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____3275) &&
                        (let uu____3278 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____3278))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____3271
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3284 =
                        (let uu____3288 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____3288) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3294 ->
                                   match uu___10_3294 with
                                   | FStar_Syntax_Syntax.MLEFFECT -> true
                                   | uu____3297 -> false))) in
                      if uu____3284
                      then
                        let uu____3301 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____3301
                      else
                        (let uu____3306 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____3308 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____3306 uu____3308)))) in
           let dec =
             let uu____3313 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3326 ->
                       match uu___11_3326 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3333 =
                             let uu____3335 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____3335 in
                           [uu____3333]
                       | uu____3340 -> [])) in
             FStar_All.pipe_right uu____3313 (FStar_String.concat " ") in
           FStar_Util.format2 "%s%s" basic dec)
and (cflag_to_string : FStar_Syntax_Syntax.cflag -> Prims.string) =
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
    | FStar_Syntax_Syntax.DECREASES uu____3359 -> ""
and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs -> FStar_Common.string_of_list cflag_to_string fs
and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi -> term_to_string phi
and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_3369 ->
    match uu___12_3369 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____3386 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args ->
                    let uu____3423 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3448 ->
                              match uu____3448 with
                              | (t, uu____3457) -> term_to_string t)) in
                    FStar_All.pipe_right uu____3423
                      (FStar_String.concat "; "))) in
          FStar_All.pipe_right uu____3386 (FStar_String.concat "\\/") in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3474 = sli lid in
        FStar_Util.format1 "{Meta_named %s}" uu____3474
    | FStar_Syntax_Syntax.Meta_labeled (l, r, uu____3479) ->
        let uu____3484 = FStar_Range.string_of_range r in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3484
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____3495 = sli m in
        let uu____3497 = term_to_string t in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3495 uu____3497
    | FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) ->
        let uu____3507 = sli m in
        let uu____3509 = sli m' in
        let uu____3511 = term_to_string t in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3507
          uu____3509 uu____3511
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun x ->
      let uu____3526 = FStar_Options.ugly () in
      if uu____3526
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
      let uu____3547 = b in
      match uu____3547 with
      | (a, imp) ->
          let n1 =
            let uu____3555 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____3555
            then FStar_Util.JsonNull
            else
              (let uu____3560 =
                 let uu____3562 = nm_to_string a in
                 imp_to_string uu____3562 imp in
               FStar_Util.JsonStr uu____3560) in
          let t =
            let uu____3565 = term_to_string' env a.FStar_Syntax_Syntax.sort in
            FStar_Util.JsonStr uu____3565 in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env ->
    fun bs ->
      let uu____3597 = FStar_List.map (binder_to_json env) bs in
      FStar_Util.JsonList uu____3597
let (enclose_universes : Prims.string -> Prims.string) =
  fun s ->
    let uu____3615 = FStar_Options.print_universes () in
    if uu____3615 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s ->
    let uu____3631 =
      let uu____3633 = FStar_Options.ugly () in Prims.op_Negation uu____3633 in
    if uu____3631
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____3643 = s in
       match uu____3643 with
       | (us, t) ->
           let uu____3655 =
             let uu____3657 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____3657 in
           let uu____3661 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____3655 uu____3661)
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a ->
    let uu____3671 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____3673 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____3676 =
      let uu____3678 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____3678 in
    let uu____3682 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____3684 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3671 uu____3673 uu____3676
      uu____3682 uu____3684
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
          let uu____3715 =
            let uu____3717 = FStar_Options.ugly () in
            Prims.op_Negation uu____3717 in
          if uu____3715
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____3738 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____3738 (FStar_String.concat ",\n\t") in
             let uu____3753 =
               let uu____3757 =
                 let uu____3761 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____3763 =
                   let uu____3767 =
                     let uu____3769 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____3769 in
                   let uu____3773 =
                     let uu____3777 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____3780 =
                       let uu____3784 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____3786 =
                         let uu____3790 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____3792 =
                           let uu____3796 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____3798 =
                             let uu____3802 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____3804 =
                               let uu____3808 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____3810 =
                                 let uu____3814 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____3816 =
                                   let uu____3820 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____3822 =
                                     let uu____3826 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____3828 =
                                       let uu____3832 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____3834 =
                                         let uu____3838 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____3840 =
                                           let uu____3844 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____3846 =
                                             let uu____3850 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____3852 =
                                               let uu____3856 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____3858 =
                                                 let uu____3862 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____3864 =
                                                   let uu____3868 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____3868] in
                                                 uu____3862 :: uu____3864 in
                                               uu____3856 :: uu____3858 in
                                             uu____3850 :: uu____3852 in
                                           uu____3844 :: uu____3846 in
                                         uu____3838 :: uu____3840 in
                                       uu____3832 :: uu____3834 in
                                     uu____3826 :: uu____3828 in
                                   uu____3820 :: uu____3822 in
                                 uu____3814 :: uu____3816 in
                               uu____3808 :: uu____3810 in
                             uu____3802 :: uu____3804 in
                           uu____3796 :: uu____3798 in
                         uu____3790 :: uu____3792 in
                       uu____3784 :: uu____3786 in
                     uu____3777 :: uu____3780 in
                   uu____3767 :: uu____3773 in
                 uu____3761 :: uu____3763 in
               (if for_free then "_for_free " else "") :: uu____3757 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____3753)
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free ->
    fun ed -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    let basic =
      match x.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff) ->
          "#light \"off\""
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          (FStar_Pervasives_Native.None)) -> "#reset-options"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          (FStar_Pervasives_Native.Some s)) ->
          FStar_Util.format1 "#reset-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
          FStar_Util.format1 "#set-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.None)) -> "#push-options"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.Some s)) ->
          FStar_Util.format1 "#push-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions) ->
          "#pop-options"
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univs1, tps, k, uu____3942, uu____3943) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
          let binders_str = binders_to_string " " tps in
          let term_str = term_to_string k in
          let uu____3959 = FStar_Options.print_universes () in
          if uu____3959
          then
            let uu____3963 = univ_names_to_string univs1 in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____3963 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univs1, t, uu____3972, uu____3973, uu____3974) ->
          let uu____3981 = FStar_Options.print_universes () in
          if uu____3981
          then
            let uu____3985 = univ_names_to_string univs1 in
            let uu____3987 = term_to_string t in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____3985
              lid.FStar_Ident.str uu____3987
          else
            (let uu____3992 = term_to_string t in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____3992)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs1, t) ->
          let uu____3998 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
          let uu____4000 =
            let uu____4002 = FStar_Options.print_universes () in
            if uu____4002
            then
              let uu____4006 = univ_names_to_string univs1 in
              FStar_Util.format1 "<%s>" uu____4006
            else "" in
          let uu____4012 = term_to_string t in
          FStar_Util.format4 "%sval %s %s : %s" uu____3998
            lid.FStar_Ident.str uu____4000 uu____4012
      | FStar_Syntax_Syntax.Sig_assume (lid, us, f) ->
          let uu____4018 = FStar_Options.print_universes () in
          if uu____4018
          then
            let uu____4022 = univ_names_to_string us in
            let uu____4024 = term_to_string f in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____4022 uu____4024
          else
            (let uu____4029 = term_to_string f in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4029)
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____4033) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4039 = term_to_string e in
          FStar_Util.format1 "let _ = %s" uu____4039
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____4043) ->
          let uu____4052 =
            let uu____4054 = FStar_List.map sigelt_to_string ses in
            FStar_All.pipe_right uu____4054 (FStar_String.concat "\n") in
          Prims.op_Hat "(* Sig_bundle *)" uu____4052
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
            | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
                failwith "impossible"
            | (FStar_Pervasives_Native.Some lift_wp, uu____4099) -> lift_wp
            | (uu____4106, FStar_Pervasives_Native.Some lift) -> lift in
          let uu____4114 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp) in
          (match uu____4114 with
           | (us, t) ->
               let uu____4126 = lid_to_string se.FStar_Syntax_Syntax.source in
               let uu____4128 = lid_to_string se.FStar_Syntax_Syntax.target in
               let uu____4130 = univ_names_to_string us in
               let uu____4132 = term_to_string t in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____4126
                 uu____4128 uu____4130 uu____4132)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs1, tps, c, flags) ->
          let uu____4144 = FStar_Options.print_universes () in
          if uu____4144
          then
            let uu____4148 =
              let uu____4153 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____4153 in
            (match uu____4148 with
             | (univs2, t) ->
                 let uu____4167 =
                   let uu____4172 =
                     let uu____4173 = FStar_Syntax_Subst.compress t in
                     uu____4173.FStar_Syntax_Syntax.n in
                   match uu____4172 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> (bs, c1)
                   | uu____4202 -> failwith "impossible" in
                 (match uu____4167 with
                  | (tps1, c1) ->
                      let uu____4211 = sli l in
                      let uu____4213 = univ_names_to_string univs2 in
                      let uu____4215 = binders_to_string " " tps1 in
                      let uu____4218 = comp_to_string c1 in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4211
                        uu____4213 uu____4215 uu____4218))
          else
            (let uu____4223 = sli l in
             let uu____4225 = binders_to_string " " tps in
             let uu____4228 = comp_to_string c in
             FStar_Util.format3 "effect %s %s = %s" uu____4223 uu____4225
               uu____4228)
      | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
          let uu____4237 =
            let uu____4239 = FStar_List.map FStar_Ident.string_of_lid lids in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4239 in
          let uu____4249 = term_to_string t in
          FStar_Util.format2 "splice[%s] (%s)" uu____4237 uu____4249 in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____4253 ->
        let uu____4256 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs in
        Prims.op_Hat uu____4256 (Prims.op_Hat "\n" basic)
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r ->
    fun msg ->
      let uu____4273 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____4273 msg
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4284,
          { FStar_Syntax_Syntax.lbname = lb;
            FStar_Syntax_Syntax.lbunivs = uu____4286;
            FStar_Syntax_Syntax.lbtyp = t;
            FStar_Syntax_Syntax.lbeff = uu____4288;
            FStar_Syntax_Syntax.lbdef = uu____4289;
            FStar_Syntax_Syntax.lbattrs = uu____4290;
            FStar_Syntax_Syntax.lbpos = uu____4291;_}::[]),
         uu____4292)
        ->
        let uu____4315 = lbname_to_string lb in
        let uu____4317 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____4315 uu____4317
    | uu____4320 ->
        let uu____4321 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____4321 (FStar_String.concat ", ")
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m ->
    let uu____4345 = sli m.FStar_Syntax_Syntax.name in
    let uu____4347 =
      let uu____4349 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____4349 (FStar_String.concat "\n") in
    let uu____4359 =
      let uu____4361 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports in
      FStar_All.pipe_right uu____4361 (FStar_String.concat "\n") in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4345
      uu____4347 uu____4359
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
          (let uu____4405 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name in
           FStar_Util.string_builder_append strb uu____4405))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____4414 = FStar_Ident.text_of_lid lid in
           FStar_Util.string_builder_append strb uu____4414)));
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
           (let uu____4455 = f x in
            FStar_Util.string_builder_append strb uu____4455);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4464 = f x1 in
                 FStar_Util.string_builder_append strb uu____4464)) xs;
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
           (let uu____4511 = f x in
            FStar_Util.string_builder_append strb uu____4511);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4520 = f x1 in
                 FStar_Util.string_builder_append strb uu____4520)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep ->
    fun bvs ->
      let uu____4542 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs in
      binders_to_string sep uu____4542
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___13_4555 ->
    match uu___13_4555 with
    | FStar_Syntax_Syntax.ET_abstract -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h, []) -> h
    | FStar_Syntax_Syntax.ET_app (h, args) ->
        let uu____4571 =
          let uu____4573 =
            let uu____4575 =
              let uu____4577 =
                let uu____4579 = FStar_List.map emb_typ_to_string args in
                FStar_All.pipe_right uu____4579 (FStar_String.concat " ") in
              Prims.op_Hat uu____4577 ")" in
            Prims.op_Hat " " uu____4575 in
          Prims.op_Hat h uu____4573 in
        Prims.op_Hat "(" uu____4571
    | FStar_Syntax_Syntax.ET_fun (a, b) ->
        let uu____4594 =
          let uu____4596 = emb_typ_to_string a in
          let uu____4598 =
            let uu____4600 = emb_typ_to_string b in
            Prims.op_Hat ") -> " uu____4600 in
          Prims.op_Hat uu____4596 uu____4598 in
        Prims.op_Hat "(" uu____4594