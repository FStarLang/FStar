open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___0_4 ->
    match uu___0_4 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____6 = FStar_Util.string_of_int i in
        Prims.op_Hat "Delta_constant_at_level " uu____6
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____8 = FStar_Util.string_of_int i in
        Prims.op_Hat "Delta_equational_at_level " uu____8
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____10 =
          let uu____11 = delta_depth_to_string d in Prims.op_Hat uu____11 ")" in
        Prims.op_Hat "Delta_abstract (" uu____10
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l ->
    let uu____17 = FStar_Options.print_real_names () in
    if uu____17
    then FStar_Ident.string_of_lid l
    else
      (let uu____19 = FStar_Ident.ident_of_lid l in
       FStar_Ident.string_of_id uu____19)
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l -> sli l
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____35 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    let uu____36 =
      let uu____37 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.op_Hat "#" uu____37 in
    Prims.op_Hat uu____35 uu____36
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____43 = FStar_Options.print_real_names () in
    if uu____43
    then bv_to_string bv
    else FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv ->
    let uu____50 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    let uu____51 =
      let uu____52 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.op_Hat "@" uu____52 in
    Prims.op_Hat uu____50 uu____51
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
      | uu____190 -> false
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____201 -> failwith "get_lid"
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
  'uuuuuu273 'uuuuuu274 .
    ('uuuuuu273, 'uuuuuu274) FStar_Util.either -> Prims.bool
  =
  fun uu___1_283 ->
    match uu___1_283 with
    | FStar_Util.Inl uu____288 -> false
    | FStar_Util.Inr uu____289 -> true
let filter_imp :
  'uuuuuu294 .
    ('uuuuuu294 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuuu294 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___2_349 ->
            match uu___2_349 with
            | (uu____356, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta
               (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t))) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____362, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____363)) -> false
            | (uu____366, FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____367)) -> false
            | uu____370 -> true))
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e ->
    let uu____386 =
      let uu____387 = FStar_Syntax_Subst.compress e in
      uu____387.FStar_Syntax_Syntax.n in
    match uu____386 with
    | FStar_Syntax_Syntax.Tm_app (f, args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____448 =
          (is_lex_cons f) && ((FStar_List.length exps) = (Prims.of_int (2))) in
        if uu____448
        then
          let uu____453 =
            let uu____458 = FStar_List.nth exps Prims.int_one in
            reconstruct_lex uu____458 in
          (match uu____453 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____468 =
                 let uu____471 = FStar_List.nth exps Prims.int_zero in
                 uu____471 :: xs in
               FStar_Pervasives_Native.Some uu____468
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____481 ->
        let uu____482 = is_lex_top e in
        if uu____482
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f ->
    fun l ->
      match l with
      | [] -> failwith "blah"
      | hd::tl -> let uu____523 = f hd in if uu____523 then hd else find f tl
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x ->
    fun xs ->
      let uu____547 =
        find
          (fun p -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____547
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____571 = get_lid e in find_lid uu____571 infix_prim_ops
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e -> let uu____581 = get_lid e in find_lid uu____581 unary_prim_ops
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t -> let uu____591 = get_lid t in find_lid uu____591 quants
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x -> FStar_Parser_Const.const_to_string x
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___3_601 ->
    match uu___3_601 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u ->
    let uu____609 = FStar_Options.hide_uvar_nums () in
    if uu____609
    then "?"
    else
      (let uu____611 =
         let uu____612 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____612 FStar_Util.string_of_int in
       Prims.op_Hat "?" uu____611)
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v ->
    let uu____618 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.major in
    let uu____619 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____618 uu____619
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    -> Prims.string)
  =
  fun u ->
    let uu____645 = FStar_Options.hide_uvar_nums () in
    if uu____645
    then "?"
    else
      (let uu____647 =
         let uu____648 =
           let uu____649 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____649 FStar_Util.string_of_int in
         let uu____650 =
           let uu____651 =
             FStar_All.pipe_right u
               (fun uu____666 ->
                  match uu____666 with
                  | (uu____677, u1, uu____679) -> version_to_string u1) in
           Prims.op_Hat ":" uu____651 in
         Prims.op_Hat uu____648 uu____650 in
       Prims.op_Hat "?" uu____647)
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n ->
    fun u ->
      let uu____704 = FStar_Syntax_Subst.compress_univ u in
      match uu____704 with
      | FStar_Syntax_Syntax.U_zero -> (n, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 -> int_of_univ (n + Prims.int_one) u1
      | uu____714 -> (n, (FStar_Pervasives_Native.Some u))
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u ->
    let uu____722 = FStar_Syntax_Subst.compress_univ u in
    match uu____722 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____734 = univ_uvar_to_string u1 in
        Prims.op_Hat "U_unif " uu____734
    | FStar_Syntax_Syntax.U_name x ->
        let uu____736 = FStar_Ident.string_of_id x in
        Prims.op_Hat "U_name " uu____736
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____738 = FStar_Util.string_of_int x in
        Prims.op_Hat "@" uu____738
    | FStar_Syntax_Syntax.U_zero -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____740 = int_of_univ Prims.int_one u1 in
        (match uu____740 with
         | (n, FStar_Pervasives_Native.None) -> FStar_Util.string_of_int n
         | (n, FStar_Pervasives_Native.Some u2) ->
             let uu____754 = univ_to_string u2 in
             let uu____755 = FStar_Util.string_of_int n in
             FStar_Util.format2 "(%s + %s)" uu____754 uu____755)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____759 =
          let uu____760 = FStar_List.map univ_to_string us in
          FStar_All.pipe_right uu____760 (FStar_String.concat ", ") in
        FStar_Util.format1 "(max %s)" uu____759
    | FStar_Syntax_Syntax.U_unknown -> "unknown"
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us ->
    let uu____770 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____770 (FStar_String.concat ", ")
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us ->
    let uu____780 = FStar_List.map (fun x -> FStar_Ident.string_of_id x) us in
    FStar_All.pipe_right uu____780 (FStar_String.concat ", ")
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___4_791 ->
    match uu___4_791 with
    | FStar_Syntax_Syntax.Assumption -> "assume"
    | FStar_Syntax_Syntax.New -> "new"
    | FStar_Syntax_Syntax.Private -> "private"
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> "unfold"
    | FStar_Syntax_Syntax.Inline_for_extraction -> "inline"
    | FStar_Syntax_Syntax.NoExtract -> "noextract"
    | FStar_Syntax_Syntax.Visible_default -> "visible"
    | FStar_Syntax_Syntax.Irreducible -> "irreducible"
    | FStar_Syntax_Syntax.Noeq -> "noeq"
    | FStar_Syntax_Syntax.Unopteq -> "unopteq"
    | FStar_Syntax_Syntax.Logic -> "logic"
    | FStar_Syntax_Syntax.TotalEffect -> "total"
    | FStar_Syntax_Syntax.Discriminator l ->
        let uu____793 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____793
    | FStar_Syntax_Syntax.Projector (l, x) ->
        let uu____796 = lid_to_string l in
        let uu____797 = FStar_Ident.string_of_id x in
        FStar_Util.format2 "(Projector %s %s)" uu____796 uu____797
    | FStar_Syntax_Syntax.RecordType (ns, fns) ->
        let uu____808 =
          let uu____809 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____809 in
        let uu____810 =
          let uu____811 =
            FStar_All.pipe_right fns
              (FStar_List.map FStar_Ident.string_of_id) in
          FStar_All.pipe_right uu____811 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____808 uu____810
    | FStar_Syntax_Syntax.RecordConstructor (ns, fns) ->
        let uu____830 =
          let uu____831 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____831 in
        let uu____832 =
          let uu____833 =
            FStar_All.pipe_right fns
              (FStar_List.map FStar_Ident.string_of_id) in
          FStar_All.pipe_right uu____833 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____830 uu____832
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____843 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____843
    | FStar_Syntax_Syntax.ExceptionConstructor -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect -> "Effect"
    | FStar_Syntax_Syntax.Reifiable -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        let uu____845 = FStar_Ident.string_of_lid l in
        FStar_Util.format1 "(reflect %s)" uu____845
    | FStar_Syntax_Syntax.OnlyName -> "OnlyName"
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu____855 ->
        let uu____858 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____858 (FStar_String.concat " ")
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals ->
    match quals with
    | [] -> ""
    | uu____876 ->
        let uu____879 = quals_to_string quals in Prims.op_Hat uu____879 " "
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.op_Hat "(" (Prims.op_Hat s ")")
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1029 = db_to_string x in
        Prims.op_Hat "Tm_bvar: " uu____1029
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1031 = nm_to_string x in
        Prims.op_Hat "Tm_name: " uu____1031
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1033 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.op_Hat "Tm_fvar: " uu____1033
    | FStar_Syntax_Syntax.Tm_uinst uu____1034 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1041 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1042 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1043,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
           FStar_Syntax_Syntax.antiquotes = uu____1044;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1057,
         { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
           FStar_Syntax_Syntax.antiquotes = uu____1058;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1071 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1090 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1105 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1112 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1129 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1152 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1179 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1192 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed uu____1205 -> "Tm_delayed"
    | FStar_Syntax_Syntax.Tm_meta (uu____1220, m) ->
        let uu____1226 = metadata_to_string m in
        Prims.op_Hat "Tm_meta:" uu____1226
    | FStar_Syntax_Syntax.Tm_unknown -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1227 -> "Tm_lazy"
and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x ->
    let uu____1229 =
      let uu____1230 = FStar_Options.ugly () in Prims.op_Negation uu____1230 in
    if uu____1229
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1238 = FStar_Options.print_implicits () in
         if uu____1238 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1242 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1257, []) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1281, thunk);
             FStar_Syntax_Syntax.ltyp = uu____1283;
             FStar_Syntax_Syntax.rng = uu____1284;_}
           ->
           let uu____1295 =
             let uu____1296 =
               let uu____1297 = FStar_Thunk.force thunk in
               term_to_string uu____1297 in
             Prims.op_Hat uu____1296 "]" in
           Prims.op_Hat "[LAZYEMB:" uu____1295
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1301 =
             let uu____1302 =
               let uu____1303 =
                 let uu____1304 =
                   let uu____1313 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
                   FStar_Util.must uu____1313 in
                 uu____1304 i.FStar_Syntax_Syntax.lkind i in
               term_to_string uu____1303 in
             Prims.op_Hat uu____1302 "]" in
           Prims.op_Hat "[lazy:" uu____1301
       | FStar_Syntax_Syntax.Tm_quoted (tm, qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static ->
                let print_aq uu____1365 =
                  match uu____1365 with
                  | (bv, t) ->
                      let uu____1372 = bv_to_string bv in
                      let uu____1373 = term_to_string t in
                      FStar_Util.format2 "%s -> %s" uu____1372 uu____1373 in
                let uu____1374 = term_to_string tm in
                let uu____1375 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes in
                FStar_Util.format2 "`(%s)%s" uu____1374 uu____1375
            | FStar_Syntax_Syntax.Quote_dynamic ->
                let uu____1382 = term_to_string tm in
                FStar_Util.format1 "quote (%s)" uu____1382)
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_pattern (uu____1384, ps)) ->
           let pats =
             let uu____1423 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args ->
                       let uu____1457 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1479 ->
                                 match uu____1479 with
                                 | (t1, uu____1487) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1457
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1423 (FStar_String.concat "\\/") in
           let uu____1496 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1496
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_monadic (m, t')) ->
           let uu____1508 = tag_of_term t in
           let uu____1509 = sli m in
           let uu____1510 = term_to_string t' in
           let uu____1511 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1508 uu____1509
             uu____1510 uu____1511
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_monadic_lift (m0, m1, t')) ->
           let uu____1524 = tag_of_term t in
           let uu____1525 = term_to_string t' in
           let uu____1526 = sli m0 in
           let uu____1527 = sli m1 in
           let uu____1528 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1524
             uu____1525 uu____1526 uu____1527 uu____1528
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_labeled (l, r, b)) ->
           let uu____1537 = FStar_Range.string_of_range r in
           let uu____1538 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1537
             uu____1538
       | FStar_Syntax_Syntax.Tm_meta (t, FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1545 = lid_to_string l in
           let uu____1546 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1547 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1545 uu____1546
             uu____1547
       | FStar_Syntax_Syntax.Tm_meta
           (t, FStar_Syntax_Syntax.Meta_desugared uu____1549) ->
           let uu____1554 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1554
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1556 = db_to_string x3 in
           let uu____1557 =
             let uu____1558 =
               let uu____1559 = tag_of_term x3.FStar_Syntax_Syntax.sort in
               Prims.op_Hat uu____1559 ")" in
             Prims.op_Hat ":(" uu____1558 in
           Prims.op_Hat uu____1556 uu____1557
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u, ([], uu____1563)) ->
           let uu____1578 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ()) in
           if uu____1578
           then ctx_uvar_to_string_aux true u
           else
             (let uu____1580 =
                let uu____1581 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1581 in
              Prims.op_Hat "?" uu____1580)
       | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
           let uu____1600 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ()) in
           if uu____1600
           then
             let uu____1601 = ctx_uvar_to_string_aux true u in
             let uu____1602 =
               let uu____1603 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s) in
               FStar_All.pipe_right uu____1603 (FStar_String.concat "; ") in
             FStar_Util.format2 "(%s @ %s)" uu____1601 uu____1602
           else
             (let uu____1615 =
                let uu____1616 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1616 in
              Prims.op_Hat "?" uu____1615)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1619 = FStar_Options.print_universes () in
           if uu____1619
           then
             let uu____1620 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1620
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
           let uu____1644 = binders_to_string " -> " bs in
           let uu____1645 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1644 uu____1645
       | FStar_Syntax_Syntax.Tm_abs (bs, t2, lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1674 = binders_to_string " " bs in
                let uu____1675 = term_to_string t2 in
                let uu____1676 =
                  FStar_Ident.string_of_lid
                    rc.FStar_Syntax_Syntax.residual_effect in
                let uu____1677 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1681 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1681) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1674 uu____1675 uu____1676 uu____1677
            | uu____1684 ->
                let uu____1687 = binders_to_string " " bs in
                let uu____1688 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1687 uu____1688)
       | FStar_Syntax_Syntax.Tm_refine (xt, f) ->
           let uu____1695 = bv_to_string xt in
           let uu____1696 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1697 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1695 uu____1696 uu____1697
       | FStar_Syntax_Syntax.Tm_app (t, args) ->
           let uu____1726 = term_to_string t in
           let uu____1727 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1726 uu____1727
       | FStar_Syntax_Syntax.Tm_let (lbs, e) ->
           let uu____1746 = lbs_to_string [] lbs in
           let uu____1747 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1746 uu____1747
       | FStar_Syntax_Syntax.Tm_ascribed (e, (annot, topt), eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1808 =
                   let uu____1809 =
                     FStar_Util.map_opt eff_name FStar_Ident.string_of_lid in
                   FStar_All.pipe_right uu____1809
                     (FStar_Util.dflt "default") in
                 let uu____1814 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1808 uu____1814
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1830 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1830 in
           let uu____1831 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1831 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head, branches) ->
           let uu____1870 = term_to_string head in
           let uu____1871 =
             let uu____1872 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string) in
             FStar_Util.concat_l "\n\t|" uu____1872 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1870 uu____1871
       | FStar_Syntax_Syntax.Tm_uinst (t, us) ->
           let uu____1885 = FStar_Options.print_universes () in
           if uu____1885
           then
             let uu____1886 = term_to_string t in
             let uu____1887 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1886 uu____1887
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown -> "_")
and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____1889 ->
    match uu____1889 with
    | (p, wopt, e) ->
        let uu____1909 = FStar_All.pipe_right p pat_to_string in
        let uu____1910 =
          match wopt with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____1918 = FStar_All.pipe_right w term_to_string in
              FStar_Util.format1 "when %s" uu____1918 in
        let uu____1919 = FStar_All.pipe_right e term_to_string in
        FStar_Util.format3 "%s %s -> %s" uu____1909 uu____1910 uu____1919
and (ctx_uvar_to_string_aux :
  Prims.bool -> FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun print_reason ->
    fun ctx_uvar ->
      let reason_string =
        if print_reason
        then
          FStar_Util.format1 "(* %s *)\n"
            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason
        else
          (let uu____1924 =
             let uu____1925 =
               FStar_Range.start_of_range
                 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_range in
             FStar_Range.string_of_pos uu____1925 in
           let uu____1926 =
             let uu____1927 =
               FStar_Range.end_of_range
                 ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_range in
             FStar_Range.string_of_pos uu____1927 in
           FStar_Util.format2 "(%s-%s) " uu____1924 uu____1926) in
      let uu____1928 =
        binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders in
      let uu____1929 =
        uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
      let uu____1930 =
        term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ in
      FStar_Util.format4 "%s(%s |- %s : %s)" reason_string uu____1928
        uu____1929 uu____1930
and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_1931 ->
    match uu___5_1931 with
    | FStar_Syntax_Syntax.DB (i, x) ->
        let uu____1934 = FStar_Util.string_of_int i in
        let uu____1935 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1934 uu____1935
    | FStar_Syntax_Syntax.NM (x, i) ->
        let uu____1938 = bv_to_string x in
        let uu____1939 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1938 uu____1939
    | FStar_Syntax_Syntax.NT (x, t) ->
        let uu____1946 = bv_to_string x in
        let uu____1947 = term_to_string t in
        FStar_Util.format2 "NT (%s, %s)" uu____1946 uu____1947
    | FStar_Syntax_Syntax.UN (i, u) ->
        let uu____1950 = FStar_Util.string_of_int i in
        let uu____1951 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1950 uu____1951
    | FStar_Syntax_Syntax.UD (u, i) ->
        let uu____1954 = FStar_Ident.string_of_id u in
        let uu____1955 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" uu____1954 uu____1955
and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s ->
    let uu____1957 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1957 (FStar_String.concat "; ")
and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x ->
    let uu____1967 =
      let uu____1968 = FStar_Options.ugly () in Prims.op_Negation uu____1968 in
    if uu____1967
    then
      let e =
        let uu____1970 = FStar_Syntax_Syntax.new_bv_set () in
        FStar_Syntax_Resugar.resugar_pat x uu____1970 in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l, pats) ->
           let uu____1993 = fv_to_string l in
           let uu____1994 =
             let uu____1995 =
               FStar_List.map
                 (fun uu____2006 ->
                    match uu____2006 with
                    | (x1, b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.op_Hat "#" p else p) pats in
             FStar_All.pipe_right uu____1995 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1993 uu____1994
       | FStar_Syntax_Syntax.Pat_dot_term (x1, uu____2018) ->
           let uu____2023 = FStar_Options.print_bound_var_types () in
           if uu____2023
           then
             let uu____2024 = bv_to_string x1 in
             let uu____2025 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____2024 uu____2025
           else
             (let uu____2027 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____2027)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2029 = FStar_Options.print_bound_var_types () in
           if uu____2029
           then
             let uu____2030 = bv_to_string x1 in
             let uu____2031 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____2030 uu____2031
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2035 = FStar_Options.print_bound_var_types () in
           if uu____2035
           then
             let uu____2036 = bv_to_string x1 in
             let uu____2037 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "_wild_%s:%s" uu____2036 uu____2037
           else bv_to_string x1)
and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals ->
    fun lbs ->
      let uu____2043 = quals_to_string' quals in
      let uu____2044 =
        let uu____2045 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb ->
                  let uu____2061 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs in
                  let uu____2062 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____2063 =
                    let uu____2064 = FStar_Options.print_universes () in
                    if uu____2064
                    then
                      let uu____2065 =
                        let uu____2066 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.op_Hat uu____2066 ">" in
                      Prims.op_Hat "<" uu____2065
                    else "" in
                  let uu____2068 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____2069 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2061
                    uu____2062 uu____2063 uu____2068 uu____2069)) in
        FStar_Util.concat_l "\n and " uu____2045 in
      FStar_Util.format3 "%slet %s %s" uu____2043
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2044
and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2073 ->
    match uu___6_2073 with
    | [] -> ""
    | tms ->
        let uu____2079 =
          let uu____2080 =
            FStar_List.map
              (fun t -> let uu____2086 = term_to_string t in paren uu____2086)
              tms in
          FStar_All.pipe_right uu____2080 (FStar_String.concat "; ") in
        FStar_Util.format1 "[@ %s]" uu____2079
and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s ->
    fun uu___7_2090 ->
      match uu___7_2090 with
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
          let uu____2099 =
            let uu____2100 = term_to_string t in
            Prims.op_Hat uu____2100 (Prims.op_Hat "]" s) in
          Prims.op_Hat "#[" uu____2099
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____2104 =
            let uu____2105 = term_to_string t in
            Prims.op_Hat uu____2105 (Prims.op_Hat "]" s) in
          Prims.op_Hat "#[@@" uu____2104
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
      let uu____2118 =
        let uu____2119 = FStar_Options.ugly () in
        Prims.op_Negation uu____2119 in
      if uu____2118
      then
        let uu____2120 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____2120 with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
        (let uu____2126 = b in
         match uu____2126 with
         | (a, imp) ->
             let uu____2139 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____2139
             then
               let uu____2140 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.op_Hat "_:" uu____2140
             else
               (let uu____2142 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2144 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____2144) in
                if uu____2142
                then
                  let uu____2145 = nm_to_string a in
                  imp_to_string uu____2145 imp
                else
                  (let uu____2147 =
                     let uu____2148 = nm_to_string a in
                     let uu____2149 =
                       let uu____2150 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.op_Hat ":" uu____2150 in
                     Prims.op_Hat uu____2148 uu____2149 in
                   imp_to_string uu____2147 imp)))
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
        let uu____2164 = FStar_Options.print_implicits () in
        if uu____2164 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____2168 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____2168 (FStar_String.concat sep)
      else
        (let uu____2190 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____2190 (FStar_String.concat sep))
and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_2199 ->
    match uu___8_2199 with
    | (a, imp) ->
        let uu____2212 = term_to_string a in imp_to_string uu____2212 imp
and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args ->
    let args1 =
      let uu____2223 = FStar_Options.print_implicits () in
      if uu____2223 then args else filter_imp args in
    let uu____2235 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2235 (FStar_String.concat " ")
and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c ->
    let uu____2257 =
      let uu____2258 = FStar_Options.ugly () in Prims.op_Negation uu____2258 in
    if uu____2257
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t, uopt) ->
           let uu____2272 =
             let uu____2273 = FStar_Syntax_Subst.compress t in
             uu____2273.FStar_Syntax_Syntax.n in
           (match uu____2272 with
            | FStar_Syntax_Syntax.Tm_type uu____2276 when
                let uu____2277 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2277 -> term_to_string t
            | uu____2278 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2280 = univ_to_string u in
                     let uu____2281 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2280 uu____2281
                 | uu____2282 ->
                     let uu____2285 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2285))
       | FStar_Syntax_Syntax.GTotal (t, uopt) ->
           let uu____2296 =
             let uu____2297 = FStar_Syntax_Subst.compress t in
             uu____2297.FStar_Syntax_Syntax.n in
           (match uu____2296 with
            | FStar_Syntax_Syntax.Tm_type uu____2300 when
                let uu____2301 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2301 -> term_to_string t
            | uu____2302 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2304 = univ_to_string u in
                     let uu____2305 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2304 uu____2305
                 | uu____2306 ->
                     let uu____2309 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2309))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2312 = FStar_Options.print_effect_args () in
             if uu____2312
             then
               let uu____2313 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2314 =
                 let uu____2315 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2315 (FStar_String.concat ", ") in
               let uu____2324 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2325 =
                 let uu____2326 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2326 (FStar_String.concat ", ") in
               let uu____2347 = cflags_to_string c1.FStar_Syntax_Syntax.flags in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2313
                 uu____2314 uu____2324 uu____2325 uu____2347
             else
               (let uu____2349 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_2353 ->
                           match uu___9_2353 with
                           | FStar_Syntax_Syntax.TOTAL -> true
                           | uu____2354 -> false)))
                    &&
                    (let uu____2356 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2356) in
                if uu____2349
                then
                  let uu____2357 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2357
                else
                  (let uu____2359 =
                     ((let uu____2362 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2362) &&
                        (let uu____2364 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2364))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2359
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2366 =
                        (let uu____2369 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2369) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_2373 ->
                                   match uu___10_2373 with
                                   | FStar_Syntax_Syntax.MLEFFECT -> true
                                   | uu____2374 -> false))) in
                      if uu____2366
                      then
                        let uu____2375 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2375
                      else
                        (let uu____2377 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2378 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2377 uu____2378)))) in
           let dec =
             let uu____2380 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_2390 ->
                       match uu___11_2390 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2396 =
                             let uu____2397 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2397 in
                           [uu____2396]
                       | uu____2398 -> [])) in
             FStar_All.pipe_right uu____2380 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2402 -> ""
and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs -> FStar_Common.string_of_list cflag_to_string fs
and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi -> term_to_string phi
and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_2411 ->
    match uu___12_2411 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____2412, ps) ->
        let pats =
          let uu____2447 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args ->
                    let uu____2481 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2503 ->
                              match uu____2503 with
                              | (t, uu____2511) -> term_to_string t)) in
                    FStar_All.pipe_right uu____2481
                      (FStar_String.concat "; "))) in
          FStar_All.pipe_right uu____2447 (FStar_String.concat "\\/") in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2521 = sli lid in
        FStar_Util.format1 "{Meta_named %s}" uu____2521
    | FStar_Syntax_Syntax.Meta_labeled (l, r, uu____2524) ->
        let uu____2525 = FStar_Range.string_of_range r in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2525
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m, t) ->
        let uu____2533 = sli m in
        let uu____2534 = term_to_string t in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2533 uu____2534
    | FStar_Syntax_Syntax.Meta_monadic_lift (m, m', t) ->
        let uu____2542 = sli m in
        let uu____2543 = sli m' in
        let uu____2544 = term_to_string t in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2542
          uu____2543 uu____2544
let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq -> aqual_to_string' "" aq
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env ->
    fun c ->
      let uu____2560 = FStar_Options.ugly () in
      if uu____2560
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
      let uu____2574 = FStar_Options.ugly () in
      if uu____2574
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
      let uu____2588 = b in
      match uu____2588 with
      | (a, imp) ->
          let n =
            let uu____2596 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____2596
            then FStar_Util.JsonNull
            else
              (let uu____2598 =
                 let uu____2599 = nm_to_string a in
                 imp_to_string uu____2599 imp in
               FStar_Util.JsonStr uu____2598) in
          let t =
            let uu____2601 = term_to_string' env a.FStar_Syntax_Syntax.sort in
            FStar_Util.JsonStr uu____2601 in
          FStar_Util.JsonAssoc [("name", n); ("type", t)]
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env ->
    fun bs ->
      let uu____2624 = FStar_List.map (binder_to_json env) bs in
      FStar_Util.JsonList uu____2624
let (enclose_universes : Prims.string -> Prims.string) =
  fun s ->
    let uu____2638 = FStar_Options.print_universes () in
    if uu____2638 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s ->
    let uu____2645 =
      let uu____2646 = FStar_Options.ugly () in Prims.op_Negation uu____2646 in
    if uu____2645
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
      (let uu____2650 = s in
       match uu____2650 with
       | (us, t) ->
           let uu____2661 =
             let uu____2662 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2662 in
           let uu____2663 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2661 uu____2663)
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a ->
    let uu____2669 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2670 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2671 =
      let uu____2672 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2672 in
    let uu____2673 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2674 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2669 uu____2670 uu____2671
      uu____2673 uu____2674
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs ->
    let tscheme_opt_to_string uu___13_2687 =
      match uu___13_2687 with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None -> "None" in
    let uu____2691 =
      let uu____2694 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp in
      let uu____2695 =
        let uu____2698 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp in
        let uu____2699 =
          let uu____2702 =
            tscheme_to_string combs.FStar_Syntax_Syntax.stronger in
          let uu____2703 =
            let uu____2706 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else in
            let uu____2707 =
              let uu____2710 =
                tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp in
              let uu____2711 =
                let uu____2714 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp in
                let uu____2715 =
                  let uu____2718 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial in
                  let uu____2719 =
                    let uu____2722 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr in
                    let uu____2723 =
                      let uu____2726 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr in
                      let uu____2727 =
                        let uu____2730 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr in
                        [uu____2730] in
                      uu____2726 :: uu____2727 in
                    uu____2722 :: uu____2723 in
                  uu____2718 :: uu____2719 in
                uu____2714 :: uu____2715 in
              uu____2710 :: uu____2711 in
            uu____2706 :: uu____2707 in
          uu____2702 :: uu____2703 in
        uu____2698 :: uu____2699 in
      uu____2694 :: uu____2695 in
    FStar_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu____2691
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs ->
    let to_str uu____2745 =
      match uu____2745 with
      | (ts_t, ts_ty) ->
          let uu____2752 = tscheme_to_string ts_t in
          let uu____2753 = tscheme_to_string ts_ty in
          FStar_Util.format2 "(%s) : (%s)" uu____2752 uu____2753 in
    let uu____2754 =
      let uu____2757 = to_str combs.FStar_Syntax_Syntax.l_repr in
      let uu____2758 =
        let uu____2761 = to_str combs.FStar_Syntax_Syntax.l_return in
        let uu____2762 =
          let uu____2765 = to_str combs.FStar_Syntax_Syntax.l_bind in
          let uu____2766 =
            let uu____2769 = to_str combs.FStar_Syntax_Syntax.l_subcomp in
            let uu____2770 =
              let uu____2773 =
                to_str combs.FStar_Syntax_Syntax.l_if_then_else in
              [uu____2773] in
            uu____2769 :: uu____2770 in
          uu____2765 :: uu____2766 in
        uu____2761 :: uu____2762 in
      uu____2757 :: uu____2758 in
    FStar_Util.format
      "{\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  }\n"
      uu____2754
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___14_2778 ->
    match uu___14_2778 with
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
          let uu____2806 =
            let uu____2807 = FStar_Options.ugly () in
            Prims.op_Negation uu____2807 in
          if uu____2806
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
               let uu____2821 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2821 (FStar_String.concat ",\n\t") in
             let eff_name =
               let uu____2831 = FStar_Syntax_Util.is_layered ed in
               if uu____2831 then "layered_effect" else "new_effect" in
             let uu____2833 =
               let uu____2836 =
                 let uu____2839 =
                   let uu____2842 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname in
                   let uu____2843 =
                     let uu____2846 =
                       let uu____2847 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                       FStar_All.pipe_left enclose_universes uu____2847 in
                     let uu____2848 =
                       let uu____2851 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                       let uu____2852 =
                         let uu____2855 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature in
                         let uu____2856 =
                           let uu____2859 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators in
                           let uu____2860 =
                             let uu____2863 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions in
                             [uu____2863] in
                           uu____2859 :: uu____2860 in
                         uu____2855 :: uu____2856 in
                       uu____2851 :: uu____2852 in
                     uu____2846 :: uu____2848 in
                   uu____2842 :: uu____2843 in
                 (if for_free then "_for_free " else "") :: uu____2839 in
               eff_name :: uu____2836 in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu____2833)
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free ->
    fun ed -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
        let uu____2890 = FStar_All.pipe_right ts_opt FStar_Util.must in
        FStar_All.pipe_right uu____2890 tscheme_to_string
      else "<None>" in
    let uu____2894 = lid_to_string se.FStar_Syntax_Syntax.source in
    let uu____2895 = lid_to_string se.FStar_Syntax_Syntax.target in
    let uu____2896 = tsopt_to_string se.FStar_Syntax_Syntax.lift in
    let uu____2897 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____2894 uu____2895 uu____2896 uu____2897
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
          (lid, univs, tps, k, uu____2911, uu____2912) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
          let binders_str = binders_to_string " " tps in
          let term_str = term_to_string k in
          let uu____2924 = FStar_Options.print_universes () in
          if uu____2924
          then
            let uu____2925 = FStar_Ident.string_of_lid lid in
            let uu____2926 = univ_names_to_string univs in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str uu____2925
              uu____2926 binders_str term_str
          else
            (let uu____2928 = FStar_Ident.string_of_lid lid in
             FStar_Util.format4 "%stype %s %s : %s" quals_str uu____2928
               binders_str term_str)
      | FStar_Syntax_Syntax.Sig_datacon
          (lid, univs, t, uu____2932, uu____2933, uu____2934) ->
          let uu____2939 = FStar_Options.print_universes () in
          if uu____2939
          then
            let uu____2940 = univ_names_to_string univs in
            let uu____2941 = FStar_Ident.string_of_lid lid in
            let uu____2942 = term_to_string t in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____2940 uu____2941
              uu____2942
          else
            (let uu____2944 = FStar_Ident.string_of_lid lid in
             let uu____2945 = term_to_string t in
             FStar_Util.format2 "datacon %s : %s" uu____2944 uu____2945)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t) ->
          let uu____2949 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
          let uu____2950 = FStar_Ident.string_of_lid lid in
          let uu____2951 =
            let uu____2952 = FStar_Options.print_universes () in
            if uu____2952
            then
              let uu____2953 = univ_names_to_string univs in
              FStar_Util.format1 "<%s>" uu____2953
            else "" in
          let uu____2955 = term_to_string t in
          FStar_Util.format4 "%sval %s %s : %s" uu____2949 uu____2950
            uu____2951 uu____2955
      | FStar_Syntax_Syntax.Sig_assume (lid, us, f) ->
          let uu____2959 = FStar_Options.print_universes () in
          if uu____2959
          then
            let uu____2960 = FStar_Ident.string_of_lid lid in
            let uu____2961 = univ_names_to_string us in
            let uu____2962 = term_to_string f in
            FStar_Util.format3 "val %s<%s> : %s" uu____2960 uu____2961
              uu____2962
          else
            (let uu____2964 = FStar_Ident.string_of_lid lid in
             let uu____2965 = term_to_string f in
             FStar_Util.format2 "val %s : %s" uu____2964 uu____2965)
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____2967) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_bundle (ses, uu____2973) ->
          let uu____2982 =
            let uu____2983 = FStar_List.map sigelt_to_string ses in
            FStar_All.pipe_right uu____2983 (FStar_String.concat "\n") in
          Prims.op_Hat "(* Sig_bundle *)" uu____2982
      | FStar_Syntax_Syntax.Sig_fail (errs, lax, ses) ->
          let uu____2999 = FStar_Util.string_of_bool lax in
          let uu____3000 =
            FStar_Common.string_of_list FStar_Util.string_of_int errs in
          let uu____3001 =
            let uu____3002 = FStar_List.map sigelt_to_string ses in
            FStar_All.pipe_right uu____3002 (FStar_String.concat "\n") in
          FStar_Util.format3 "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n"
            uu____2999 uu____3000 uu____3001
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____3008 = FStar_Syntax_Util.is_dm4f ed in
          eff_decl_to_string' uu____3008 x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l, univs, tps, c, flags) ->
          let uu____3019 = FStar_Options.print_universes () in
          if uu____3019
          then
            let uu____3020 =
              let uu____3025 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Range.dummyRange in
              FStar_Syntax_Subst.open_univ_vars univs uu____3025 in
            (match uu____3020 with
             | (univs1, t) ->
                 let uu____3038 =
                   let uu____3043 =
                     let uu____3044 = FStar_Syntax_Subst.compress t in
                     uu____3044.FStar_Syntax_Syntax.n in
                   match uu____3043 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs, c1) -> (bs, c1)
                   | uu____3073 -> failwith "impossible" in
                 (match uu____3038 with
                  | (tps1, c1) ->
                      let uu____3080 = sli l in
                      let uu____3081 = univ_names_to_string univs1 in
                      let uu____3082 = binders_to_string " " tps1 in
                      let uu____3083 = comp_to_string c1 in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____3080
                        uu____3081 uu____3082 uu____3083))
          else
            (let uu____3085 = sli l in
             let uu____3086 = binders_to_string " " tps in
             let uu____3087 = comp_to_string c in
             FStar_Util.format3 "effect %s %s = %s" uu____3085 uu____3086
               uu____3087)
      | FStar_Syntax_Syntax.Sig_splice (lids, t) ->
          let uu____3094 =
            let uu____3095 = FStar_List.map FStar_Ident.string_of_lid lids in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____3095 in
          let uu____3100 = term_to_string t in
          FStar_Util.format2 "splice[%s] (%s)" uu____3094 uu____3100
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m, n, p, t, ty) ->
          let uu____3106 = FStar_Ident.string_of_lid m in
          let uu____3107 = FStar_Ident.string_of_lid n in
          let uu____3108 = FStar_Ident.string_of_lid p in
          let uu____3109 = tscheme_to_string t in
          let uu____3110 = tscheme_to_string ty in
          FStar_Util.format5 "polymonadic_bind (%s, %s) |> %s = (%s, %s)"
            uu____3106 uu____3107 uu____3108 uu____3109 uu____3110
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp (m, n, t, ty) ->
          let uu____3115 = FStar_Ident.string_of_lid m in
          let uu____3116 = FStar_Ident.string_of_lid n in
          let uu____3117 = tscheme_to_string t in
          let uu____3118 = tscheme_to_string ty in
          FStar_Util.format4 "polymonadic_subcomp %s <: %s = (%s, %s)"
            uu____3115 uu____3116 uu____3117 uu____3118 in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____3119 ->
        let uu____3122 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs in
        Prims.op_Hat uu____3122 (Prims.op_Hat "\n" basic)
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r ->
    fun msg ->
      let uu____3133 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____3133 msg
let (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3139,
          { FStar_Syntax_Syntax.lbname = lb;
            FStar_Syntax_Syntax.lbunivs = uu____3141;
            FStar_Syntax_Syntax.lbtyp = t;
            FStar_Syntax_Syntax.lbeff = uu____3143;
            FStar_Syntax_Syntax.lbdef = uu____3144;
            FStar_Syntax_Syntax.lbattrs = uu____3145;
            FStar_Syntax_Syntax.lbpos = uu____3146;_}::[]),
         uu____3147)
        ->
        let uu____3168 = lbname_to_string lb in
        let uu____3169 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____3168 uu____3169
    | uu____3170 ->
        let uu____3171 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l -> FStar_Ident.string_of_lid l)) in
        FStar_All.pipe_right uu____3171 (FStar_String.concat ", ")
let (tag_of_sigelt : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____3187 -> "Sig_inductive_typ"
    | FStar_Syntax_Syntax.Sig_bundle uu____3204 -> "Sig_bundle"
    | FStar_Syntax_Syntax.Sig_datacon uu____3213 -> "Sig_datacon"
    | FStar_Syntax_Syntax.Sig_declare_typ uu____3228 -> "Sig_declare_typ"
    | FStar_Syntax_Syntax.Sig_let uu____3235 -> "Sig_let"
    | FStar_Syntax_Syntax.Sig_assume uu____3242 -> "Sig_assume"
    | FStar_Syntax_Syntax.Sig_new_effect uu____3249 -> "Sig_new_effect"
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3250 -> "Sig_sub_effect"
    | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3251 -> "Sig_effect_abbrev"
    | FStar_Syntax_Syntax.Sig_pragma uu____3264 -> "Sig_pragma"
    | FStar_Syntax_Syntax.Sig_splice uu____3265 -> "Sig_splice"
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3272 ->
        "Sig_polymonadic_bind"
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____3283 ->
        "Sig_polymonadic_subcomp"
    | FStar_Syntax_Syntax.Sig_fail uu____3292 -> "Sig_fail"
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m ->
    let uu____3308 = sli m.FStar_Syntax_Syntax.name in
    let uu____3309 =
      let uu____3310 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3310 (FStar_String.concat "\n") in
    let uu____3315 =
      let uu____3316 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3316 (FStar_String.concat "\n") in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____3308
      uu____3309 uu____3315
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f ->
    fun elts ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "[";
           (let uu____3354 = f x in
            FStar_Util.string_builder_append strb uu____3354);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3361 = f x1 in
                 FStar_Util.string_builder_append strb uu____3361)) xs;
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
           (let uu____3399 = f x in
            FStar_Util.string_builder_append strb uu____3399);
           FStar_List.iter
             (fun x1 ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3406 = f x1 in
                 FStar_Util.string_builder_append strb uu____3406)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep ->
    fun bvs ->
      let uu____3422 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs in
      binders_to_string sep uu____3422
let (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar -> ctx_uvar_to_string_aux true ctx_uvar
let (ctx_uvar_to_string_no_reason :
  FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar -> ctx_uvar_to_string_aux false ctx_uvar
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___15_3443 ->
    match uu___15_3443 with
    | FStar_Syntax_Syntax.ET_abstract -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h, []) -> h
    | FStar_Syntax_Syntax.ET_app (h, args) ->
        let uu____3453 =
          let uu____3454 =
            let uu____3455 =
              let uu____3456 =
                let uu____3457 = FStar_List.map emb_typ_to_string args in
                FStar_All.pipe_right uu____3457 (FStar_String.concat " ") in
              Prims.op_Hat uu____3456 ")" in
            Prims.op_Hat " " uu____3455 in
          Prims.op_Hat h uu____3454 in
        Prims.op_Hat "(" uu____3453
    | FStar_Syntax_Syntax.ET_fun (a, b) ->
        let uu____3464 =
          let uu____3465 = emb_typ_to_string a in
          let uu____3466 =
            let uu____3467 = emb_typ_to_string b in
            Prims.op_Hat ") -> " uu____3467 in
          Prims.op_Hat uu____3465 uu____3466 in
        Prims.op_Hat "(" uu____3464