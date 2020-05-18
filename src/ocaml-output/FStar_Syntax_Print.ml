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
    then FStar_Ident.string_of_lid l
    else
      (let uu____38 = FStar_Ident.ident_of_lid l in
       FStar_Ident.string_of_id uu____38)
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l -> sli l
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____60 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    let uu____62 =
      let uu____64 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.op_Hat "#" uu____64 in
    Prims.op_Hat uu____60 uu____62
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____74 = FStar_Options.print_real_names () in
    if uu____74
    then bv_to_string bv
    else FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____87 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    let uu____89 =
      let uu____91 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.op_Hat "@" uu____91 in
    Prims.op_Hat uu____87 uu____89
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
      | uu____313 -> false
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____326 -> failwith "get_lid"
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
  'uuuuuu429 'uuuuuu430 .
    ('uuuuuu429, 'uuuuuu430) FStar_Util.either -> Prims.bool
  =
  fun uu___1_440 ->
    match uu___1_440 with
    | FStar_Util.Inl uu____445 -> false
    | FStar_Util.Inr uu____447 -> true
let filter_imp :
  'uuuuuu454 .
    ('uuuuuu454 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuuu454 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___2_509 ->
            match uu___2_509 with
            | (uu____517, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta
               (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t))) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____524, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____525)) -> false
            | (uu____530, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____531)) -> false
            | uu____535 -> true))
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e ->
    let uu____553 =
      let uu____554 = FStar_Syntax_Subst.compress e in
      uu____554.FStar_Syntax_Syntax.n in
    match uu____553 with
    | FStar_Syntax_Syntax.Tm_app (f, args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____615 =
          (is_lex_cons f) && ((FStar_List.length exps) = (Prims.of_int (2))) in
        if uu____615
        then
          let uu____624 =
            let uu____629 = FStar_List.nth exps Prims.int_one in
            reconstruct_lex uu____629 in
          (match uu____624 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____640 =
                 let uu____643 = FStar_List.nth exps Prims.int_zero in
                 uu____643 :: xs in
               FStar_Pervasives_Native.Some uu____640
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____655 ->
        let uu____656 = is_lex_top e in
        if uu____656
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f ->
    fun l ->
      match l with
      | [] -> failwith "blah"
      | hd::tl -> let uu____704 = f hd in if uu____704 then hd else find f tl
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x ->
    fun xs ->
      let uu____736 =
        find
          (fun p -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____736
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____767 = get_lid e in find_lid uu____767 infix_prim_ops
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____779 = get_lid e in find_lid uu____779 unary_prim_ops
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t -> let uu____791 = get_lid t in find_lid uu____791 quants
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x -> FStar_Parser_Const.const_to_string x
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___3_805 ->
    match uu___3_805 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u ->
    let uu____816 = FStar_Options.hide_uvar_nums () in
    if uu____816
    then "?"
    else
      (let uu____823 =
         let uu____825 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____825 FStar_Util.string_of_int in
       Prims.op_Hat "?" uu____823)
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v ->
    let uu____837 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.major in
    let uu____839 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____837 uu____839
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    -> Prims.string)
  =
  fun u ->
    let uu____869 = FStar_Options.hide_uvar_nums () in
    if uu____869
    then "?"
    else
      (let uu____876 =
         let uu____878 =
           let uu____880 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____880 FStar_Util.string_of_int in
         let uu____884 =
           let uu____886 =
             FStar_All.pipe_right u
               (fun uu____903 ->
                  match uu____903 with
                  | (uu____915, u1, uu____917) -> version_to_string u1) in
           Prims.op_Hat ":" uu____886 in
         Prims.op_Hat uu____878 uu____884 in
       Prims.op_Hat "?" uu____876)
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n ->
    fun u ->
      let uu____948 = FStar_Syntax_Subst.compress_univ u in
      match uu____948 with
      | FStar_Syntax_Syntax.U_zero -> (n, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 -> int_of_univ (n + Prims.int_one) u1
      | uu____961 -> (n, (FStar_Pervasives_Native.Some u))
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u ->
    let uu____972 = FStar_Syntax_Subst.compress_univ u in
    match uu____972 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____985 = univ_uvar_to_string u1 in
        Prims.op_Hat "U_unif " uu____985
    | FStar_Syntax_Syntax.U_name x ->
        let uu____989 = FStar_Ident.string_of_id x in
        Prims.op_Hat "U_name " uu____989
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____994 = FStar_Util.string_of_int x in
        Prims.op_Hat "@" uu____994
    | FStar_Syntax_Syntax.U_zero -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____999 = int_of_univ Prims.int_one u1 in
        (match uu____999 with
         | (n, FStar_Pervasives_Native.None) -> FStar_Util.string_of_int n
         | (n, FStar_Pervasives_Native.Some u2) ->
             let uu____1020 = univ_to_string u2 in
             let uu____1022 = FStar_Util.string_of_int n in
             FStar_Util.format2 "(%s + %s)" uu____1020 uu____1022)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____1028 =
          let uu____1030 = FStar_List.map univ_to_string us in
          FStar_All.pipe_right uu____1030 (FStar_String.concat ", ") in
        FStar_Util.format1 "(max %s)" uu____1028
    | FStar_Syntax_Syntax.U_unknown -> "unknown"
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us ->
    let uu____1049 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____1049 (FStar_String.concat ", ")
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us ->
    let uu____1066 = FStar_List.map (fun x -> FStar_Ident.string_of_id x) us in
    FStar_All.pipe_right uu____1066 (FStar_String.concat ", ")
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___4_1084 ->
    match uu___4_1084 with
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
        let uu____1100 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1100
    | FStar_Syntax_Syntax.Projector (l, x) ->
        let uu____1105 = lid_to_string l in
        let uu____1107 = FStar_Ident.string_of_id x in
        FStar_Util.format2 "(Projector %s %s)" uu____1105 uu____1107
    | FStar_Syntax_Syntax.RecordType (ns, fns) ->
        let uu____1120 =
          let uu____1122 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1122 in
        let uu____1123 =
          let uu____1125 =
            FStar_All.pipe_right fns
              (FStar_List.map FStar_Ident.string_of_id) in
          FStar_All.pipe_right uu____1125 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1120 uu____1123
    | FStar_Syntax_Syntax.RecordConstructor (ns, fns) ->
        let uu____1151 =
          let uu____1153 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1153 in
        let uu____1154 =
          let uu____1156 =
            FStar_All.pipe_right fns
              (FStar_List.map FStar_Ident.string_of_id) in
          FStar_All.pipe_right uu____1156 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1151 uu____1154
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1173 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1173
    | FStar_Syntax_Syntax.ExceptionConstructor -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect -> "Effect"
    | FStar_Syntax_Syntax.Reifiable -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        let uu____1181 = FStar_Ident.string_of_lid l in
        FStar_Util.format1 "(reflect %s)" uu____1181
    | FStar_Syntax_Syntax.OnlyName -> "OnlyName"
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu____1198 ->
        let uu____1201 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1201 (FStar_String.concat " ")
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu____1229 ->
        let uu____1232 = quals_to_string quals in Prims.op_Hat uu____1232 " "
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.op_Hat "(" (Prims.op_Hat s ")")
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1414 = db_to_string x in
        Prims.op_Hat "Tm_bvar: " uu____1414
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1418 = nm_to_string x in
        Prims.op_Hat "Tm_name: " uu____1418
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1422 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.op_Hat "Tm_fvar: " uu____1422
    | FStar_Syntax_Syntax.Tm_uinst uu____1425 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1433 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1435 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1437,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
           FStar_Syntax_Syntax.antiquotes = uu____1438;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1452,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
           FStar_Syntax_Syntax.antiquotes = uu____1453;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1467 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1487 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1503 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1511 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1529 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1553 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1581 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1596 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed uu____1610 -> "Tm_delayed"
    | FStar_Syntax_Syntax.Tm_meta (uu____1626, m) ->
        let uu____1632 = metadata_to_string m in
        Prims.op_Hat "Tm_meta:" uu____1632
    | FStar_Syntax_Syntax.Tm_unknown -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1636 -> "Tm_lazy"
and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x ->
    let uu____1639 =
      let uu____1641 = FStar_Options.ugly () in Prims.op_Negation uu____1641 in
    if uu____1639
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1655 = FStar_Options.print_implicits () in
         if uu____1655 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1663 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1680, []) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1706, thunk);
             FStar_Syntax_Syntax.ltyp = uu____1708;
             FStar_Syntax_Syntax.rng = uu____1709;_}
           ->
           let uu____1720 =
             let uu____1722 =
               let uu____1724 = FStar_Thunk.force thunk in
               term_to_string uu____1724 in
             Prims.op_Hat uu____1722 "]" in
           Prims.op_Hat "[LAZYEMB:" uu____1720
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1730 =
             let uu____1732 =
               let uu____1734 =
                 let uu____1735 =
                   let uu____1744 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
                   FStar_Util.must uu____1744 in
                 uu____1735 i.FStar_Syntax_Syntax.lkind i in
               term_to_string uu____1734 in
             Prims.op_Hat uu____1732 "]" in
           Prims.op_Hat "[lazy:" uu____1730
       | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static ->
                let print_aq uu____1813 =
                  match uu____1813 with
                  | (bv, t) ->
                      let uu____1821 = bv_to_string bv in
                      let uu____1823 = term_to_string t in
                      FStar_Util.format2 "%s -> %s" uu____1821 uu____1823 in
                let uu____1826 = term_to_string tm in
                let uu____1828 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes in
                FStar_Util.format2 "`(%s)%s" uu____1826 uu____1828
            | FStar_Syntax_Syntax.Quote_dynamic ->
                let uu____1837 = term_to_string tm in
                FStar_Util.format1 "quote (%s)" uu____1837)
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_pattern (uu____1841, ps)) ->
           let pats =
             let uu____1881 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args ->
                       let uu____1918 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1943 ->
                                 match uu____1943 with
                                 | (t1, uu____1952) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1918
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1881 (FStar_String.concat "\\/") in
           let uu____1967 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1967
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) ->
           let uu____1981 = tag_of_term t in
           let uu____1983 = sli m in
           let uu____1985 = term_to_string t' in
           let uu____1987 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1981 uu____1983
             uu____1985 uu____1987
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) ->
           let uu____2002 = tag_of_term t in
           let uu____2004 = term_to_string t' in
           let uu____2006 = sli m0 in
           let uu____2008 = sli m1 in
           let uu____2010 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2002
             uu____2004 uu____2006 uu____2008 uu____2010
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) ->
           let uu____2025 = FStar_Range.string_of_range r in
           let uu____2027 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2025
             uu____2027
       | FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2036 = lid_to_string l in
           let uu____2038 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____2040 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2036 uu____2038
             uu____2040
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_desugared uu____2044) ->
           let uu____2049 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2049
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2053 = db_to_string x3 in
           let uu____2055 =
             let uu____2057 =
               let uu____2059 = tag_of_term x3.FStar_Syntax_Syntax.sort in
               Prims.op_Hat uu____2059 ")" in
             Prims.op_Hat ":(" uu____2057 in
           Prims.op_Hat uu____2053 uu____2055
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u, ([], uu____2066)) ->
           let uu____2081 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ()) in
           if uu____2081
           then ctx_uvar_to_string u
           else
             (let uu____2087 =
                let uu____2089 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2089 in
              Prims.op_Hat "?" uu____2087)
       | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
           let uu____2112 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ()) in
           if uu____2112
           then
             let uu____2116 = ctx_uvar_to_string u in
             let uu____2118 =
               let uu____2120 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s) in
               FStar_All.pipe_right uu____2120 (FStar_String.concat "; ") in
             FStar_Util.format2 "(%s @ %s)" uu____2116 uu____2118
           else
             (let uu____2139 =
                let uu____2141 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2141 in
              Prims.op_Hat "?" uu____2139)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2148 = FStar_Options.print_universes () in
           if uu____2148
           then
             let uu____2152 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____2152
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
           let uu____2180 = binders_to_string " -> " bs in
           let uu____2183 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____2180 uu____2183
       | FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2215 = binders_to_string " " bs in
                let uu____2218 = term_to_string t2 in
                let uu____2220 =
                  FStar_Ident.string_of_lid
                    rc.FStar_Syntax_Syntax.residual_effect in
                let uu____2222 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2231 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____2231) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2215 uu____2218 uu____2220 uu____2222
            | uu____2235 ->
                let uu____2238 = binders_to_string " " bs in
                let uu____2241 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____2238 uu____2241)
       | FStar_Syntax_Syntax.Tm_refine (xt, f) ->
           let uu____2250 = bv_to_string xt in
           let uu____2252 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____2255 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____2250 uu____2252 uu____2255
       | FStar_Syntax_Syntax.Tm_app (t, args) ->
           let uu____2287 = term_to_string t in
           let uu____2289 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____2287 uu____2289
       | FStar_Syntax_Syntax.Tm_let (lbs, e) ->
           let uu____2312 = lbs_to_string [] lbs in
           let uu____2314 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____2312 uu____2314
       | FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2379 =
                   let uu____2381 =
                     FStar_Util.map_opt eff_name FStar_Ident.string_of_lid in
                   FStar_All.pipe_right uu____2381
                     (FStar_Util.dflt "default") in
                 let uu____2392 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____2379 uu____2392
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2413 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____2413 in
           let uu____2416 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2416 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head, branches) ->
           let uu____2457 = term_to_string head in
           let uu____2459 =
             let uu____2461 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string) in
             FStar_Util.concat_l "\n\t|" uu____2461 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2457 uu____2459
       | FStar_Syntax_Syntax.Tm_uinst (t, us) ->
           let uu____2479 = FStar_Options.print_universes () in
           if uu____2479
           then
             let uu____2483 = term_to_string t in
             let uu____2485 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____2483 uu____2485
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown -> "_")
and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____2491 ->
    match uu____2491 with
    | (p, wopt, e) ->
        let uu____2513 = FStar_All.pipe_right p pat_to_string in
        let uu____2516 =
          match wopt with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____2527 = FStar_All.pipe_right w term_to_string in
              FStar_Util.format1 "when %s" uu____2527 in
        let uu____2531 = FStar_All.pipe_right e term_to_string in
        FStar_Util.format3 "%s %s -> %s" uu____2513 uu____2516 uu____2531
and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar ->
    let uu____2536 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders in
    let uu____2539 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
    let uu____2541 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2536 uu____2539
      uu____2541
and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2544 ->
    match uu___5_2544 with
    | FStar_Syntax_Syntax.DB (i, x) ->
        let uu____2550 = FStar_Util.string_of_int i in
        let uu____2552 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2550 uu____2552
    | FStar_Syntax_Syntax.NM (x, i) ->
        let uu____2559 = bv_to_string x in
        let uu____2561 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2559 uu____2561
    | FStar_Syntax_Syntax.NT (x, t) ->
        let uu____2570 = bv_to_string x in
        let uu____2572 = term_to_string t in
        FStar_Util.format2 "NT (%s, %s)" uu____2570 uu____2572
    | FStar_Syntax_Syntax.UN (i, u) ->
        let uu____2579 = FStar_Util.string_of_int i in
        let uu____2581 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2579 uu____2581
    | FStar_Syntax_Syntax.UD (u, i) ->
        let uu____2588 = FStar_Ident.string_of_id u in
        let uu____2590 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" uu____2588 uu____2590
and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s ->
    let uu____2594 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2594 (FStar_String.concat "; ")
and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x ->
    let uu____2610 =
      let uu____2612 = FStar_Options.ugly () in Prims.op_Negation uu____2612 in
    if uu____2610
    then
      let e =
        let uu____2617 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Syntax_Resugar.resugar_pat x uu____2617 in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l, pats) ->
           let uu____2646 = fv_to_string l in
           let uu____2648 =
             let uu____2650 =
               FStar_List.map
                 (fun uu____2664 ->
                    match uu____2664 with
                    | (x1, b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.op_Hat "#" p else p) pats in
             FStar_All.pipe_right uu____2650 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____2646 uu____2648
       | FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2689) ->
           let uu____2694 = FStar_Options.print_bound_var_types () in
           if uu____2694
           then
             let uu____2698 = bv_to_string x1 in
             let uu____2700 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____2698 uu____2700
           else
             (let uu____2705 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____2705)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2709 = FStar_Options.print_bound_var_types () in
           if uu____2709
           then
             let uu____2713 = bv_to_string x1 in
             let uu____2715 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____2713 uu____2715
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2722 = FStar_Options.print_bound_var_types () in
           if uu____2722
           then
             let uu____2726 = bv_to_string x1 in
             let uu____2728 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "_wild_%s:%s" uu____2726 uu____2728
           else bv_to_string x1)
and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals ->
    fun lbs ->
      let uu____2737 = quals_to_string' quals in
      let uu____2739 =
        let uu____2741 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb ->
                  let uu____2761 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs in
                  let uu____2763 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____2765 =
                    let uu____2767 = FStar_Options.print_universes () in
                    if uu____2767
                    then
                      let uu____2771 =
                        let uu____2773 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.op_Hat uu____2773 ">" in
                      Prims.op_Hat "<" uu____2771
                    else "" in
                  let uu____2780 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____2782 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2761
                    uu____2763 uu____2765 uu____2780 uu____2782)) in
        FStar_Util.concat_l "\n and " uu____2741 in
      FStar_Util.format3 "%slet %s %s" uu____2737
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2739
and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2797 ->
    match uu___6_2797 with
    | [] -> ""
    | tms ->
        let uu____2805 =
          let uu____2807 =
            FStar_List.map
              (fun t -> let uu____2815 = term_to_string t in paren uu____2815)
              tms in
          FStar_All.pipe_right uu____2807 (FStar_String.concat "; ") in
        FStar_Util.format1 "[@ %s]" uu____2805
and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s ->
    fun uu___7_2824 ->
      match uu___7_2824 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false))
          -> Prims.op_Hat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true)) ->
          Prims.op_Hat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
          Prims.op_Hat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.op_Hat "[|" (Prims.op_Hat s "|]")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
          let uu____2842 =
            let uu____2844 = term_to_string t in
            Prims.op_Hat uu____2844 (Prims.op_Hat "]" s) in
          Prims.op_Hat "#[" uu____2842
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____2851 =
            let uu____2853 = term_to_string t in
            Prims.op_Hat uu____2853 (Prims.op_Hat "]" s) in
          Prims.op_Hat "#[@@" uu____2851
      | FStar_Pervasives_Native.None -> s
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
      let uu____2871 =
        let uu____2873 = FStar_Options.ugly () in
        Prims.op_Negation uu____2873 in
      if uu____2871
      then
        let uu____2877 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____2877 with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
        (let uu____2888 = b in
         match uu____2888 with
         | (a, imp) ->
             let uu____2902 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____2902
             then
               let uu____2906 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.op_Hat "_:" uu____2906
             else
               (let uu____2911 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2914 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____2914) in
                if uu____2911
                then
                  let uu____2918 = nm_to_string a in
                  imp_to_string uu____2918 imp
                else
                  (let uu____2922 =
                     let uu____2924 = nm_to_string a in
                     let uu____2926 =
                       let uu____2928 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.op_Hat ":" uu____2928 in
                     Prims.op_Hat uu____2924 uu____2926 in
                   imp_to_string uu____2922 imp)))
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
        let uu____2947 = FStar_Options.print_implicits () in
        if uu____2947 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____2958 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____2958 (FStar_String.concat sep)
      else
        (let uu____2986 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____2986 (FStar_String.concat sep))
and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_3000 ->
    match uu___8_3000 with
    | (a, imp) ->
        let uu____3014 = term_to_string a in imp_to_string uu____3014 imp
and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args ->
    let args1 =
      let uu____3026 = FStar_Options.print_implicits () in
      if uu____3026 then args else filter_imp args in
    let uu____3041 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____3041 (FStar_String.concat " ")
and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    let uu____3069 =
      let uu____3071 = FStar_Options.ugly () in Prims.op_Negation uu____3071 in
    if uu____3069
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t, uopt) ->
           let uu____3092 =
             let uu____3093 = FStar_Syntax_Subst.compress t in
             uu____3093.FStar_Syntax_Syntax.n in
           (match uu____3092 with
            | FStar_Syntax_Syntax.Tm_type uu____3097 when
                let uu____3098 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____3098 -> term_to_string t
            | uu____3100 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3103 = univ_to_string u in
                     let uu____3105 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____3103 uu____3105
                 | uu____3108 ->
                     let uu____3111 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____3111))
       | FStar_Syntax_Syntax.GTotal (t, uopt) ->
           let uu____3124 =
             let uu____3125 = FStar_Syntax_Subst.compress t in
             uu____3125.FStar_Syntax_Syntax.n in
           (match uu____3124 with
            | FStar_Syntax_Syntax.Tm_type uu____3129 when
                let uu____3130 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____3130 -> term_to_string t
            | uu____3132 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3135 = univ_to_string u in
                     let uu____3137 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____3135 uu____3137
                 | uu____3140 ->
                     let uu____3143 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____3143))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3149 = FStar_Options.print_effect_args () in
             if uu____3149
             then
               let uu____3153 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____3155 =
                 let uu____3157 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____3157 (FStar_String.concat ", ") in
               let uu____3172 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____3174 =
                 let uu____3176 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____3176 (FStar_String.concat ", ") in
               let uu____3203 = cflags_to_string c1.FStar_Syntax_Syntax.flags in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3153
                 uu____3155 uu____3172 uu____3174 uu____3203
             else
               (let uu____3208 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3214 ->
                           match uu___9_3214 with
                           | FStar_Syntax_Syntax.TOTAL -> true
                           | uu____3217 -> false)))
                    &&
                    (let uu____3220 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____3220) in
                if uu____3208
                then
                  let uu____3224 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____3224
                else
                  (let uu____3229 =
                     ((let uu____3233 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____3233) &&
                        (let uu____3236 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____3236))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____3229
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3242 =
                        (let uu____3246 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____3246) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3252 ->
                                   match uu___10_3252 with
                                   | FStar_Syntax_Syntax.MLEFFECT -> true
                                   | uu____3255 -> false))) in
                      if uu____3242
                      then
                        let uu____3259 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____3259
                      else
                        (let uu____3264 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____3266 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____3264 uu____3266)))) in
           let dec =
             let uu____3271 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3284 ->
                       match uu___11_3284 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3291 =
                             let uu____3293 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____3293 in
                           [uu____3291]
                       | uu____3298 -> [])) in
             FStar_All.pipe_right uu____3271 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____3317 -> ""
and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs -> FStar_Common.string_of_list cflag_to_string fs
and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi -> term_to_string phi
and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_3327 ->
    match uu___12_3327 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____3329, ps) ->
        let pats =
          let uu____3365 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args ->
                    let uu____3402 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3427 ->
                              match uu____3427 with
                              | (t, uu____3436) -> term_to_string t)) in
                    FStar_All.pipe_right uu____3402
                      (FStar_String.concat "; "))) in
          FStar_All.pipe_right uu____3365 (FStar_String.concat "\\/") in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3453 = sli lid in
        FStar_Util.format1 "{Meta_named %s}" uu____3453
    | FStar_Syntax_Syntax.Meta_labeled (l, r, uu____3458) ->
        let uu____3463 = FStar_Range.string_of_range r in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3463
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____3474 = sli m in
        let uu____3476 = term_to_string t in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3474 uu____3476
    | FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) ->
        let uu____3486 = sli m in
        let uu____3488 = sli m' in
        let uu____3490 = term_to_string t in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3486
          uu____3488 uu____3490
let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq -> aqual_to_string' "" aq
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let uu____3513 = FStar_Options.ugly () in
      if uu____3513
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c in
         let d = FStar_Parser_ToDocument.term_to_document e in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env ->
    fun x ->
      let uu____3535 = FStar_Options.ugly () in
      if uu____3535
      then term_to_string x
      else
        (let e = FStar_Syntax_Resugar.resugar_term' env x in
         let d = FStar_Parser_ToDocument.term_to_document e in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)
let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env ->
    fun b ->
      let uu____3556 = b in
      match uu____3556 with
      | (a, imp) ->
          let n =
            let uu____3564 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____3564
            then FStar_Util.JsonNull
            else
              (let uu____3569 =
                 let uu____3571 = nm_to_string a in
                 imp_to_string uu____3571 imp in
               FStar_Util.JsonStr uu____3569) in
          let t =
            let uu____3574 = term_to_string' env a.FStar_Syntax_Syntax.sort in
            FStar_Util.JsonStr uu____3574 in
          FStar_Util.JsonAssoc [("name", n); ("type", t)]
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env ->
    fun bs ->
      let uu____3606 = FStar_List.map (binder_to_json env) bs in
      FStar_Util.JsonList uu____3606
let (enclose_universes : Prims.string -> Prims.string) =
  fun s ->
    let uu____3624 = FStar_Options.print_universes () in
    if uu____3624 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s ->
    let uu____3640 =
      let uu____3642 = FStar_Options.ugly () in Prims.op_Negation uu____3642 in
    if uu____3640
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
      (let uu____3652 = s in
       match uu____3652 with
       | (us, t) ->
           let uu____3664 =
             let uu____3666 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____3666 in
           let uu____3670 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____3664 uu____3670)
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a ->
    let uu____3680 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____3682 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____3685 =
      let uu____3687 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____3687 in
    let uu____3691 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____3693 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3680 uu____3682 uu____3685
      uu____3691 uu____3693
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs ->
    let tscheme_opt_to_string uu___13_3711 =
      match uu___13_3711 with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None -> "None" in
    let uu____3717 =
      let uu____3721 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp in
      let uu____3723 =
        let uu____3727 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp in
        let uu____3729 =
          let uu____3733 =
            tscheme_to_string combs.FStar_Syntax_Syntax.stronger in
          let uu____3735 =
            let uu____3739 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else in
            let uu____3741 =
              let uu____3745 =
                tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp in
              let uu____3747 =
                let uu____3751 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp in
                let uu____3753 =
                  let uu____3757 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial in
                  let uu____3759 =
                    let uu____3763 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr in
                    let uu____3765 =
                      let uu____3769 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr in
                      let uu____3771 =
                        let uu____3775 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr in
                        [uu____3775] in
                      uu____3769 :: uu____3771 in
                    uu____3763 :: uu____3765 in
                  uu____3757 :: uu____3759 in
                uu____3751 :: uu____3753 in
              uu____3745 :: uu____3747 in
            uu____3739 :: uu____3741 in
          uu____3733 :: uu____3735 in
        uu____3727 :: uu____3729 in
      uu____3721 :: uu____3723 in
    FStar_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu____3717
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs ->
    let to_str uu____3806 =
      match uu____3806 with
      | (ts_t, ts_ty) ->
          let uu____3814 = tscheme_to_string ts_t in
          let uu____3816 = tscheme_to_string ts_ty in
          FStar_Util.format2 "(%s) : (%s)" uu____3814 uu____3816 in
    let uu____3819 =
      let uu____3823 =
        FStar_Ident.string_of_lid combs.FStar_Syntax_Syntax.l_base_effect in
      let uu____3825 =
        let uu____3829 = to_str combs.FStar_Syntax_Syntax.l_repr in
        let uu____3831 =
          let uu____3835 = to_str combs.FStar_Syntax_Syntax.l_return in
          let uu____3837 =
            let uu____3841 = to_str combs.FStar_Syntax_Syntax.l_bind in
            let uu____3843 =
              let uu____3847 = to_str combs.FStar_Syntax_Syntax.l_subcomp in
              let uu____3849 =
                let uu____3853 =
                  to_str combs.FStar_Syntax_Syntax.l_if_then_else in
                [uu____3853] in
              uu____3847 :: uu____3849 in
            uu____3841 :: uu____3843 in
          uu____3835 :: uu____3837 in
        uu____3829 :: uu____3831 in
      uu____3823 :: uu____3825 in
    FStar_Util.format
      "{\nl_base_effect = %s\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  }\n"
      uu____3819
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___14_3869 ->
    match uu___14_3869 with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        wp_eff_combinators_to_string combs
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        wp_eff_combinators_to_string combs
    | FStar_Syntax_Syntax.Layered_eff combs ->
        layered_eff_combinators_to_string combs
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
          let uu____3902 =
            let uu____3904 = FStar_Options.ugly () in
            Prims.op_Negation uu____3904 in
          if uu____3902
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
               let uu____3925 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____3925 (FStar_String.concat ",\n\t") in
             let eff_name =
               let uu____3942 = FStar_Syntax_Util.is_layered ed in
               if uu____3942 then "layered_effect" else "new_effect" in
             let uu____3950 =
               let uu____3954 =
                 let uu____3958 =
                   let uu____3962 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname in
                   let uu____3964 =
                     let uu____3968 =
                       let uu____3970 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                       FStar_All.pipe_left enclose_universes uu____3970 in
                     let uu____3974 =
                       let uu____3978 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                       let uu____3981 =
                         let uu____3985 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature in
                         let uu____3987 =
                           let uu____3991 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators in
                           let uu____3993 =
                             let uu____3997 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions in
                             [uu____3997] in
                           uu____3991 :: uu____3993 in
                         uu____3985 :: uu____3987 in
                       uu____3978 :: uu____3981 in
                     uu____3968 :: uu____3974 in
                   uu____3962 :: uu____3964 in
                 (if for_free then "_for_free " else "") :: uu____3958 in
               eff_name :: uu____3954 in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu____3950)
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free ->
    fun ed -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
        let uu____4049 = FStar_All.pipe_right ts_opt FStar_Util.must in
        FStar_All.pipe_right uu____4049 tscheme_to_string
      else "<None>" in
    let uu____4056 = lid_to_string se.FStar_Syntax_Syntax.source in
    let uu____4058 = lid_to_string se.FStar_Syntax_Syntax.target in
    let uu____4060 = tsopt_to_string se.FStar_Syntax_Syntax.lift in
    let uu____4062 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____4056 uu____4058 uu____4060 uu____4062
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
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver) ->
          "#restart-solver"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions) ->
          "#pop-options"
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid, univs, tps, k, uu____4097, uu____4098) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
          let binders_str = binders_to_string " " tps in
          let term_str = term_to_string k in
          let uu____4114 = FStar_Options.print_universes () in
          if uu____4114
          then
            let uu____4118 = FStar_Ident.string_of_lid lid in
            let uu____4120 = univ_names_to_string univs in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str uu____4118
              uu____4120 binders_str term_str
          else
            (let uu____4125 = FStar_Ident.string_of_lid lid in
             FStar_Util.format4 "%stype %s %s : %s" quals_str uu____4125
               binders_str term_str)
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univs, t, uu____4131, uu____4132, uu____4133) ->
          let uu____4140 = FStar_Options.print_universes () in
          if uu____4140
          then
            let uu____4144 = univ_names_to_string univs in
            let uu____4146 = FStar_Ident.string_of_lid lid in
            let uu____4148 = term_to_string t in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4144 uu____4146
              uu____4148
          else
            (let uu____4153 = FStar_Ident.string_of_lid lid in
             let uu____4155 = term_to_string t in
             FStar_Util.format2 "datacon %s : %s" uu____4153 uu____4155)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t) ->
          let uu____4161 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
          let uu____4163 = FStar_Ident.string_of_lid lid in
          let uu____4165 =
            let uu____4167 = FStar_Options.print_universes () in
            if uu____4167
            then
              let uu____4171 = univ_names_to_string univs in
              FStar_Util.format1 "<%s>" uu____4171
            else "" in
          let uu____4177 = term_to_string t in
          FStar_Util.format4 "%sval %s %s : %s" uu____4161 uu____4163
            uu____4165 uu____4177
      | FStar_Syntax_Syntax.Sig_assume (lid, us, f) ->
          let uu____4183 = FStar_Options.print_universes () in
          if uu____4183
          then
            let uu____4187 = FStar_Ident.string_of_lid lid in
            let uu____4189 = univ_names_to_string us in
            let uu____4191 = term_to_string f in
            FStar_Util.format3 "val %s<%s> : %s" uu____4187 uu____4189
              uu____4191
          else
            (let uu____4196 = FStar_Ident.string_of_lid lid in
             let uu____4198 = term_to_string f in
             FStar_Util.format2 "val %s : %s" uu____4196 uu____4198)
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____4202) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____4208) ->
          let uu____4217 =
            let uu____4219 = FStar_List.map sigelt_to_string ses in
            FStar_All.pipe_right uu____4219 (FStar_String.concat "\n") in
          Prims.op_Hat "(* Sig_bundle *)" uu____4217
      | FStar_Syntax_Syntax.Sig_fail (errs, lax, ses) ->
          let uu____4245 = FStar_Util.string_of_bool lax in
          let uu____4247 =
            FStar_Common.string_of_list FStar_Util.string_of_int errs in
          let uu____4250 =
            let uu____4252 = FStar_List.map sigelt_to_string ses in
            FStar_All.pipe_right uu____4252 (FStar_String.concat "\n") in
          FStar_Util.format3 "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n"
            uu____4245 uu____4247 uu____4250
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4264 = FStar_Syntax_Util.is_dm4f ed in
          eff_decl_to_string' uu____4264 x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, flags) ->
          let uu____4276 = FStar_Options.print_universes () in
          if uu____4276
          then
            let uu____4280 =
              let uu____4285 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Range.dummyRange in
              FStar_Syntax_Subst.open_univ_vars univs uu____4285 in
            (match uu____4280 with
             | (univs1, t) ->
                 let uu____4299 =
                   let uu____4304 =
                     let uu____4305 = FStar_Syntax_Subst.compress t in
                     uu____4305.FStar_Syntax_Syntax.n in
                   match uu____4304 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> (bs, c1)
                   | uu____4334 -> failwith "impossible" in
                 (match uu____4299 with
                  | (tps1, c1) ->
                      let uu____4343 = sli l in
                      let uu____4345 = univ_names_to_string univs1 in
                      let uu____4347 = binders_to_string " " tps1 in
                      let uu____4350 = comp_to_string c1 in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4343
                        uu____4345 uu____4347 uu____4350))
          else
            (let uu____4355 = sli l in
             let uu____4357 = binders_to_string " " tps in
             let uu____4360 = comp_to_string c in
             FStar_Util.format3 "effect %s %s = %s" uu____4355 uu____4357
               uu____4360)
      | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
          let uu____4369 =
            let uu____4371 = FStar_List.map FStar_Ident.string_of_lid lids in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4371 in
          let uu____4381 = term_to_string t in
          FStar_Util.format2 "splice[%s] (%s)" uu____4369 uu____4381
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m, n, p, t, ty) ->
          let uu____4389 = FStar_Ident.string_of_lid m in
          let uu____4391 = FStar_Ident.string_of_lid n in
          let uu____4393 = FStar_Ident.string_of_lid p in
          let uu____4395 = tscheme_to_string t in
          let uu____4397 = tscheme_to_string ty in
          FStar_Util.format5 "polymonadic_bind (%s, %s) |> %s = (%s, %s)"
            uu____4389 uu____4391 uu____4393 uu____4395 uu____4397 in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4403 ->
        let uu____4406 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs in
        Prims.op_Hat uu____4406 (Prims.op_Hat "\n" basic)
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r ->
    fun msg ->
      let uu____4423 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____4423 msg
let (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4434,
          { FStar_Syntax_Syntax.lbname = lb;
            FStar_Syntax_Syntax.lbunivs = uu____4436;
            FStar_Syntax_Syntax.lbtyp = t;
            FStar_Syntax_Syntax.lbeff = uu____4438;
            FStar_Syntax_Syntax.lbdef = uu____4439;
            FStar_Syntax_Syntax.lbattrs = uu____4440;
            FStar_Syntax_Syntax.lbpos = uu____4441;_}::[]),
         uu____4442)
        ->
        let uu____4465 = lbname_to_string lb in
        let uu____4467 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____4465 uu____4467
    | uu____4470 ->
        let uu____4471 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l -> FStar_Ident.string_of_lid l)) in
        FStar_All.pipe_right uu____4471 (FStar_String.concat ", ")
let (tag_of_sigelt : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4497 -> "Sig_inductive_typ"
    | FStar_Syntax_Syntax.Sig_bundle uu____4515 -> "Sig_bundle"
    | FStar_Syntax_Syntax.Sig_datacon uu____4525 -> "Sig_datacon"
    | FStar_Syntax_Syntax.Sig_declare_typ uu____4542 -> "Sig_declare_typ"
    | FStar_Syntax_Syntax.Sig_let uu____4550 -> "Sig_let"
    | FStar_Syntax_Syntax.Sig_assume uu____4558 -> "Sig_assume"
    | FStar_Syntax_Syntax.Sig_new_effect uu____4566 -> "Sig_new_effect"
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4568 -> "Sig_sub_effect"
    | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4570 -> "Sig_effect_abbrev"
    | FStar_Syntax_Syntax.Sig_pragma uu____4584 -> "Sig_pragma"
    | FStar_Syntax_Syntax.Sig_splice uu____4586 -> "Sig_splice"
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____4594 ->
        "Sig_polymonadic_bind"
    | FStar_Syntax_Syntax.Sig_fail uu____4606 -> "Sig_fail"
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m ->
    let uu____4627 = sli m.FStar_Syntax_Syntax.name in
    let uu____4629 =
      let uu____4631 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____4631 (FStar_String.concat "\n") in
    let uu____4641 =
      let uu____4643 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports in
      FStar_All.pipe_right uu____4643 (FStar_String.concat "\n") in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4627
      uu____4629 uu____4641
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f ->
    fun elts ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "[";
           (let uu____4693 = f x in
            FStar_Util.string_builder_append strb uu____4693);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4702 = f x1 in
                 FStar_Util.string_builder_append strb uu____4702)) xs;
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
           (let uu____4749 = f x in
            FStar_Util.string_builder_append strb uu____4749);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4758 = f x1 in
                 FStar_Util.string_builder_append strb uu____4758)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep ->
    fun bvs ->
      let uu____4780 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs in
      binders_to_string sep uu____4780
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___15_4793 ->
    match uu___15_4793 with
    | FStar_Syntax_Syntax.ET_abstract -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h, []) -> h
    | FStar_Syntax_Syntax.ET_app (h, args) ->
        let uu____4809 =
          let uu____4811 =
            let uu____4813 =
              let uu____4815 =
                let uu____4817 = FStar_List.map emb_typ_to_string args in
                FStar_All.pipe_right uu____4817 (FStar_String.concat " ") in
              Prims.op_Hat uu____4815 ")" in
            Prims.op_Hat " " uu____4813 in
          Prims.op_Hat h uu____4811 in
        Prims.op_Hat "(" uu____4809
    | FStar_Syntax_Syntax.ET_fun (a, b) ->
        let uu____4832 =
          let uu____4834 = emb_typ_to_string a in
          let uu____4836 =
            let uu____4838 = emb_typ_to_string b in
            Prims.op_Hat ") -> " uu____4838 in
          Prims.op_Hat uu____4834 uu____4836 in
        Prims.op_Hat "(" uu____4832