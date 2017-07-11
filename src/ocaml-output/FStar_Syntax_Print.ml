open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___204_4  ->
    match uu___204_4 with
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
      | uu____114 -> false
let get_lid:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____122 -> failwith "get_lid"
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
let is_inr uu___205_179 =
  match uu___205_179 with
  | FStar_Util.Inl uu____182 -> false
  | FStar_Util.Inr uu____183 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___206_219  ->
          match uu___206_219 with
          | (uu____223,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____224)) -> false
          | uu____226 -> true))
let rec reconstruct_lex:
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____237 =
      let uu____238 = FStar_Syntax_Subst.compress e in
      uu____238.FStar_Syntax_Syntax.n in
    match uu____237 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____272 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____272
        then
          let uu____281 =
            let uu____285 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____285 in
          (match uu____281 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____295 =
                 let uu____298 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____298 :: xs in
               FStar_Pervasives_Native.Some uu____295
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____311 ->
        let uu____312 = is_lex_top e in
        if uu____312
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____347 = f hd1 in if uu____347 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____363 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____363
let infix_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____378 = get_lid e in find_lid uu____378 infix_prim_ops
let unary_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____385 = get_lid e in find_lid uu____385 unary_prim_ops
let quant_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun t  -> let uu____392 = get_lid t in find_lid uu____392 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____401) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____404 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____409) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____419 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____419
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___207_423  ->
    match uu___207_423 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____431 = db_to_string x in Prims.strcat "Tm_bvar: " uu____431
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____433 = nm_to_string x in Prims.strcat "Tm_name: " uu____433
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____435 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____435
    | FStar_Syntax_Syntax.Tm_uinst uu____436 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____440 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____441 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____442 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____451 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____458 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____462 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____470 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____482 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____496 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____503 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____512,m) ->
        let uu____534 = FStar_ST.read m in
        (match uu____534 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____542 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____545 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____553 = FStar_Options.hide_uvar_nums () in
    if uu____553
    then "?"
    else
      (let uu____555 =
         let uu____556 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____556 FStar_Util.string_of_int in
       Prims.strcat "?" uu____555)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____561 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____562 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____561 uu____562
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____567 = FStar_Options.hide_uvar_nums () in
    if uu____567
    then "?"
    else
      (let uu____569 =
         let uu____570 =
           let uu____571 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____571 FStar_Util.string_of_int in
         let uu____572 =
           let uu____573 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____573 in
         Prims.strcat uu____570 uu____572 in
       Prims.strcat "?" uu____569)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____587 = FStar_Syntax_Subst.compress_univ u in
      match uu____587 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____593 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____599 =
      let uu____600 = FStar_Options.ugly () in Prims.op_Negation uu____600 in
    if uu____599
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____604 = FStar_Syntax_Subst.compress_univ u in
       match uu____604 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____612 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____612
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____614 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____614 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____623 = univ_to_string u2 in
                let uu____624 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____623 uu____624)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____627 =
             let uu____628 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____628 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____627
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____637 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____637 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____646 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____646 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___208_654  ->
    match uu___208_654 with
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
        let uu____656 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____656
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____659 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____659 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____666 =
          let uu____667 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____667 in
        let uu____669 =
          let uu____670 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____670 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____666 uu____669
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____681 =
          let uu____682 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____682 in
        let uu____684 =
          let uu____685 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____685 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____681 uu____684
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____691 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____691
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
    | uu____699 ->
        let uu____701 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____701 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____712 ->
        let uu____714 = quals_to_string quals in Prims.strcat uu____714 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____761 =
      let uu____762 = FStar_Options.ugly () in Prims.op_Negation uu____762 in
    if uu____761
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____768 = FStar_Options.print_implicits () in
         if uu____768 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____770 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____783,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____803 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____820 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____831  ->
                                 match uu____831 with
                                 | (t1,uu____835) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____820
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____803 (FStar_String.concat "\\/") in
           let uu____838 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____838
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____846 = tag_of_term t in
           let uu____847 = sli m in
           let uu____848 = term_to_string t' in
           let uu____849 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____846 uu____847
             uu____848 uu____849
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____858 = tag_of_term t in
           let uu____859 = term_to_string t' in
           let uu____860 = sli m0 in
           let uu____861 = sli m1 in
           let uu____862 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____858
             uu____859 uu____860 uu____861 uu____862
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____864,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____874 = FStar_Range.string_of_range r in
           let uu____875 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____874
             uu____875
       | FStar_Syntax_Syntax.Tm_meta (t,uu____877) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____881 = db_to_string x3 in
           let uu____882 =
             let uu____883 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____883 in
           Prims.strcat uu____881 uu____882
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____887) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____902 = FStar_Options.print_universes () in
           if uu____902
           then
             let uu____903 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____903
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____915 = binders_to_string " -> " bs in
           let uu____916 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____915 uu____916
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____931 = binders_to_string " " bs in
                let uu____932 = term_to_string t2 in
                let uu____933 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____936 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____936) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____931 uu____932
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____933
            | uu____938 ->
                let uu____940 = binders_to_string " " bs in
                let uu____941 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____940 uu____941)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____946 = bv_to_string xt in
           let uu____947 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____949 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____946 uu____947 uu____949
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____963 = term_to_string t in
           let uu____964 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____963 uu____964
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____975 = lbs_to_string [] lbs in
           let uu____976 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____975 uu____976
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1010 =
                   let uu____1011 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1011
                     (FStar_Util.dflt "default") in
                 let uu____1014 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1010 uu____1014
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1024 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1024 in
           let uu____1025 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1025 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1046 = term_to_string head1 in
           let uu____1047 =
             let uu____1048 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1070  ->
                       match uu____1070 with
                       | (p,wopt,e) ->
                           let uu____1080 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1081 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1083 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1083 in
                           let uu____1084 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1080
                             uu____1081 uu____1084)) in
             FStar_Util.concat_l "\n\t|" uu____1048 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1046 uu____1047
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1089 = FStar_Options.print_universes () in
           if uu____1089
           then
             let uu____1090 = term_to_string t in
             let uu____1091 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1090 uu____1091
           else term_to_string t
       | uu____1093 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1095 =
      let uu____1096 = FStar_Options.ugly () in Prims.op_Negation uu____1096 in
    if uu____1095
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1110 = fv_to_string l in
           let uu____1111 =
             let uu____1112 =
               FStar_List.map
                 (fun uu____1120  ->
                    match uu____1120 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1112 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1110 uu____1111
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1129) ->
           let uu____1132 = FStar_Options.print_bound_var_types () in
           if uu____1132
           then
             let uu____1133 = bv_to_string x1 in
             let uu____1134 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1133 uu____1134
           else
             (let uu____1136 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1136)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1138 = FStar_Options.print_bound_var_types () in
           if uu____1138
           then
             let uu____1139 = bv_to_string x1 in
             let uu____1140 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1139 uu____1140
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1144 = FStar_Options.print_real_names () in
           if uu____1144
           then
             let uu____1145 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1145
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1157 = FStar_Options.print_universes () in
        if uu____1157
        then
          let uu____1161 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1175 =
                      let uu____1178 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1178 in
                    match uu____1175 with
                    | (us,td) ->
                        let uu____1181 =
                          let uu____1186 =
                            let uu____1187 = FStar_Syntax_Subst.compress td in
                            uu____1187.FStar_Syntax_Syntax.n in
                          match uu____1186 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1193,(t,uu____1195)::(d,uu____1197)::[])
                              -> (t, d)
                          | uu____1219 -> failwith "Impossibe" in
                        (match uu____1181 with
                         | (t,d) ->
                             let uu___215_1230 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___215_1230.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___215_1230.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1161)
        else lbs in
      let uu____1234 = quals_to_string' quals in
      let uu____1235 =
        let uu____1236 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1247 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1248 =
                    let uu____1249 = FStar_Options.print_universes () in
                    if uu____1249
                    then
                      let uu____1250 =
                        let uu____1251 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1251 ">" in
                      Prims.strcat "<" uu____1250
                    else "" in
                  let uu____1253 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1254 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1247 uu____1248
                    uu____1253 uu____1254)) in
        FStar_Util.concat_l "\n and " uu____1236 in
      FStar_Util.format3 "%slet %s %s" uu____1234
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1235
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1259 = FStar_Options.print_effect_args () in
    if uu____1259
    then
      let uu____1260 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1260
    else
      (let uu____1262 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1263 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1262 uu____1263)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___209_1265  ->
      match uu___209_1265 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1267 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1271 =
        let uu____1272 = FStar_Options.ugly () in
        Prims.op_Negation uu____1272 in
      if uu____1271
      then
        let uu____1273 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1273 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1278 = b in
         match uu____1278 with
         | (a,imp) ->
             let uu____1281 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1281
             then
               let uu____1282 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1282
             else
               (let uu____1284 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1286 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1286) in
                if uu____1284
                then
                  let uu____1287 = nm_to_string a in
                  imp_to_string uu____1287 imp
                else
                  (let uu____1289 =
                     let uu____1290 = nm_to_string a in
                     let uu____1291 =
                       let uu____1292 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1292 in
                     Prims.strcat uu____1290 uu____1291 in
                   imp_to_string uu____1289 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1298 = FStar_Options.print_implicits () in
        if uu____1298 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1300 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1300 (FStar_String.concat sep)
      else
        (let uu____1305 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1305 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___210_1309  ->
    match uu___210_1309 with
    | (a,imp) ->
        let uu____1317 = term_to_string a in imp_to_string uu____1317 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1320 = FStar_Options.print_implicits () in
      if uu____1320 then args else filter_imp args in
    let uu____1323 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1323 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1331 =
      let uu____1332 = FStar_Options.ugly () in Prims.op_Negation uu____1332 in
    if uu____1331
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1342 =
             let uu____1343 = FStar_Syntax_Subst.compress t in
             uu____1343.FStar_Syntax_Syntax.n in
           (match uu____1342 with
            | FStar_Syntax_Syntax.Tm_type uu____1345 when
                let uu____1346 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1346 -> term_to_string t
            | uu____1347 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1349 = univ_to_string u in
                     let uu____1350 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1349 uu____1350
                 | uu____1351 ->
                     let uu____1353 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1353))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1360 =
             let uu____1361 = FStar_Syntax_Subst.compress t in
             uu____1361.FStar_Syntax_Syntax.n in
           (match uu____1360 with
            | FStar_Syntax_Syntax.Tm_type uu____1363 when
                let uu____1364 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1364 -> term_to_string t
            | uu____1365 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1367 = univ_to_string u in
                     let uu____1368 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1367 uu____1368
                 | uu____1369 ->
                     let uu____1371 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1371))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1374 = FStar_Options.print_effect_args () in
             if uu____1374
             then
               let uu____1375 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1376 =
                 let uu____1377 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1377 (FStar_String.concat ", ") in
               let uu____1381 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1382 =
                 let uu____1383 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1383 (FStar_String.concat ", ") in
               let uu____1394 =
                 let uu____1395 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1395 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1375
                 uu____1376 uu____1381 uu____1382 uu____1394
             else
               (let uu____1401 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___211_1404  ->
                           match uu___211_1404 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1405 -> false)))
                    &&
                    (let uu____1407 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1407) in
                if uu____1401
                then
                  let uu____1408 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1408
                else
                  (let uu____1410 =
                     ((let uu____1413 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1413) &&
                        (let uu____1415 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1415))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____1410
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1417 =
                        (let uu____1420 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1420) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___212_1423  ->
                                   match uu___212_1423 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1424 -> false))) in
                      if uu____1417
                      then
                        let uu____1425 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1425
                      else
                        (let uu____1427 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1428 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1427 uu____1428)))) in
           let dec =
             let uu____1430 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___213_1437  ->
                       match uu___213_1437 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1441 =
                             let uu____1442 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1442 in
                           [uu____1441]
                       | uu____1443 -> [])) in
             FStar_All.pipe_right uu____1430 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1446 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1454 = FStar_Options.print_universes () in
    if uu____1454 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1460 =
      let uu____1461 = FStar_Options.ugly () in Prims.op_Negation uu____1461 in
    if uu____1460
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1465 = s in
       match uu____1465 with
       | (us,t) ->
           let uu____1470 =
             let uu____1471 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1471 in
           let uu____1472 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1470 uu____1472)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____1477 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____1478 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____1479 =
      let uu____1480 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____1480 in
    let uu____1481 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____1482 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____1477 uu____1478 uu____1479
      uu____1481 uu____1482
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
          let uu____1501 =
            let uu____1502 = FStar_Options.ugly () in
            Prims.op_Negation uu____1502 in
          if uu____1501
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1512 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____1512 (FStar_String.concat ",\n\t") in
             let uu____1517 =
               let uu____1519 =
                 let uu____1521 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1522 =
                   let uu____1524 =
                     let uu____1525 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1525 in
                   let uu____1526 =
                     let uu____1528 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1529 =
                       let uu____1531 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1532 =
                         let uu____1534 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1535 =
                           let uu____1537 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1538 =
                             let uu____1540 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1541 =
                               let uu____1543 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1544 =
                                 let uu____1546 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1547 =
                                   let uu____1549 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1550 =
                                     let uu____1552 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1553 =
                                       let uu____1555 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1556 =
                                         let uu____1558 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1559 =
                                           let uu____1561 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1562 =
                                             let uu____1564 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1565 =
                                               let uu____1567 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1568 =
                                                 let uu____1570 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1571 =
                                                   let uu____1573 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1573] in
                                                 uu____1570 :: uu____1571 in
                                               uu____1567 :: uu____1568 in
                                             uu____1564 :: uu____1565 in
                                           uu____1561 :: uu____1562 in
                                         uu____1558 :: uu____1559 in
                                       uu____1555 :: uu____1556 in
                                     uu____1552 :: uu____1553 in
                                   uu____1549 :: uu____1550 in
                                 uu____1546 :: uu____1547 in
                               uu____1543 :: uu____1544 in
                             uu____1540 :: uu____1541 in
                           uu____1537 :: uu____1538 in
                         uu____1534 :: uu____1535 in
                       uu____1531 :: uu____1532 in
                     uu____1528 :: uu____1529 in
                   uu____1524 :: uu____1526 in
                 uu____1521 :: uu____1522 in
               (if for_free then "_for_free " else "") :: uu____1519 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1517)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1587 =
      let uu____1588 = FStar_Options.ugly () in Prims.op_Negation uu____1588 in
    if uu____1587
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1593 -> ""
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
           (lid,univs1,tps,k,uu____1602,uu____1603) ->
           let uu____1608 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1609 = binders_to_string " " tps in
           let uu____1610 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1608
             lid.FStar_Ident.str uu____1609 uu____1610
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1614,uu____1615,uu____1616) ->
           let uu____1619 = FStar_Options.print_universes () in
           if uu____1619
           then
             let uu____1620 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1620 with
              | (univs2,t1) ->
                  let uu____1625 = univ_names_to_string univs2 in
                  let uu____1626 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1625
                    lid.FStar_Ident.str uu____1626)
           else
             (let uu____1628 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1628)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1632 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1632 with
            | (univs2,t1) ->
                let uu____1637 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1638 =
                  let uu____1639 = FStar_Options.print_universes () in
                  if uu____1639
                  then
                    let uu____1640 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1640
                  else "" in
                let uu____1642 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1637
                  lid.FStar_Ident.str uu____1638 uu____1642)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____1644,f) ->
           let uu____1646 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1646
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1648) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1652 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1652
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1654) ->
           let uu____1659 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1659 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____1671) -> lift_wp
             | (uu____1675,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____1680 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____1680 with
            | (us,t) ->
                let uu____1687 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1688 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1689 = univ_names_to_string us in
                let uu____1690 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1687
                  uu____1688 uu____1689 uu____1690)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1698 = FStar_Options.print_universes () in
           if uu____1698
           then
             let uu____1699 =
               let uu____1702 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1702 in
             (match uu____1699 with
              | (univs2,t) ->
                  let uu____1708 =
                    let uu____1715 =
                      let uu____1716 = FStar_Syntax_Subst.compress t in
                      uu____1716.FStar_Syntax_Syntax.n in
                    match uu____1715 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1738 -> failwith "impossible" in
                  (match uu____1708 with
                   | (tps1,c1) ->
                       let uu____1755 = sli l in
                       let uu____1756 = univ_names_to_string univs2 in
                       let uu____1757 = binders_to_string " " tps1 in
                       let uu____1758 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1755
                         uu____1756 uu____1757 uu____1758))
           else
             (let uu____1760 = sli l in
              let uu____1761 = binders_to_string " " tps in
              let uu____1762 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1760 uu____1761
                uu____1762))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1771 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1771 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1776,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1778;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1780;
                       FStar_Syntax_Syntax.lbdef = uu____1781;_}::[]),uu____1782)
        ->
        let uu____1794 = lbname_to_string lb in
        let uu____1795 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____1794 uu____1795
    | uu____1796 ->
        let uu____1797 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____1797 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____1808 = sli m.FStar_Syntax_Syntax.name in
    let uu____1809 =
      let uu____1810 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____1810 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____1808 uu____1809
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___214_1816  ->
    match uu___214_1816 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1819 = FStar_Util.string_of_int i in
        let uu____1820 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____1819 uu____1820
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1823 = bv_to_string x in
        let uu____1824 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____1823 uu____1824
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1829 = bv_to_string x in
        let uu____1830 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____1829 uu____1830
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1833 = FStar_Util.string_of_int i in
        let uu____1834 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____1833 uu____1834
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1837 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1837
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____1842 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____1842 (FStar_String.concat "; ")
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
let list_to_string f elts =
  match elts with
  | [] -> "[]"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "[";
       (let uu____1896 = f x in
        FStar_Util.string_builder_append strb uu____1896);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____1903 = f x1 in
             FStar_Util.string_builder_append strb uu____1903)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____1935 = f x in
        FStar_Util.string_builder_append strb uu____1935);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____1942 = f x1 in
             FStar_Util.string_builder_append strb uu____1942)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)