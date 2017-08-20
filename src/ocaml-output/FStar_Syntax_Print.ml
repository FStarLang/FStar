open Prims
let rec (delta_depth_to_string
  :FStar_Syntax_Syntax.delta_depth -> Prims.string)=
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
let (sli :FStar_Ident.lident -> Prims.string)=
  fun l  ->
    let uu____14 = FStar_Options.print_real_names () in
    if uu____14
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let (lid_to_string :FStar_Ident.lid -> Prims.string)= fun l  -> sli l
let (fv_to_string :FStar_Syntax_Syntax.fv -> Prims.string)=
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (bv_to_string :FStar_Syntax_Syntax.bv -> Prims.string)=
  fun bv  ->
    let uu____28 =
      let uu____29 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____29 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____28
let (nm_to_string :FStar_Syntax_Syntax.bv -> Prims.string)=
  fun bv  ->
    let uu____34 = FStar_Options.print_real_names () in
    if uu____34
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let (db_to_string :FStar_Syntax_Syntax.bv -> Prims.string)=
  fun bv  ->
    let uu____40 =
      let uu____41 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____41 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____40
let (infix_prim_ops
  :(FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
     Prims.list)=
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
let (unary_prim_ops
  :(FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
     Prims.list)=
  [(FStar_Parser_Const.op_Negation, "not");
  (FStar_Parser_Const.op_Minus, "-");
  (FStar_Parser_Const.not_lid, "~")]
let (is_prim_op
  :FStar_Ident.lident Prims.list ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool)=
  fun ps  ->
    fun f  ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____177 -> false
let (get_lid
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)=
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____187 -> failwith "get_lid"
let (is_infix_prim_op :FStar_Syntax_Syntax.term -> Prims.bool)=
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
let (is_unary_prim_op :FStar_Syntax_Syntax.term -> Prims.bool)=
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
let (quants
  :(FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
     Prims.list)=
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")]
type exp = FStar_Syntax_Syntax.term
let (is_b2t :FStar_Syntax_Syntax.typ -> Prims.bool)=
  fun t  -> is_prim_op [FStar_Parser_Const.b2t_lid] t
let (is_quant :FStar_Syntax_Syntax.typ -> Prims.bool)=
  fun t  ->
    is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t
let (is_ite :FStar_Syntax_Syntax.typ -> Prims.bool)=
  fun t  -> is_prim_op [FStar_Parser_Const.ite_lid] t
let (is_lex_cons :exp -> Prims.bool)=
  fun f  -> is_prim_op [FStar_Parser_Const.lexcons_lid] f
let (is_lex_top :exp -> Prims.bool)=
  fun f  -> is_prim_op [FStar_Parser_Const.lextop_lid] f
let is_inr :
  'Auu____252 'Auu____253 .
    ('Auu____253,'Auu____252) FStar_Util.either -> Prims.bool=
  fun uu___200_261  ->
    match uu___200_261 with
    | FStar_Util.Inl uu____266 -> false
    | FStar_Util.Inr uu____267 -> true
let filter_imp :
  'Auu____272 .
    ('Auu____272,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____272,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list=
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___201_326  ->
            match uu___201_326 with
            | (uu____333,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____334)) -> false
            | uu____337 -> true))
let rec (reconstruct_lex
  :exp ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
       FStar_Pervasives_Native.option)=
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
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a=
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____529 = f hd1 in if uu____529 then hd1 else find f tl1
let (find_lid
  :FStar_Ident.lident ->
     (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
       Prims.list -> Prims.string)=
  fun x  ->
    fun xs  ->
      let uu____551 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____551
let (infix_prim_op_to_string
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string)=
  fun e  -> let uu____574 = get_lid e in find_lid uu____574 infix_prim_ops
let (unary_prim_op_to_string
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string)=
  fun e  -> let uu____583 = get_lid e in find_lid uu____583 unary_prim_ops
let (quant_to_string
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string)=
  fun t  -> let uu____592 = get_lid t in find_lid uu____592 quants
let (const_to_string :FStar_Const.sconst -> Prims.string)=
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____601) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____606 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____614) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____630 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____630
let (lbname_to_string :FStar_Syntax_Syntax.lbname -> Prims.string)=
  fun uu___202_634  ->
    match uu___202_634 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let (tag_of_term :FStar_Syntax_Syntax.term -> Prims.string)=
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____642 = db_to_string x in Prims.strcat "Tm_bvar: " uu____642
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____644 = nm_to_string x in Prims.strcat "Tm_name: " uu____644
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____646 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____646
    | FStar_Syntax_Syntax.Tm_uinst uu____647 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____654 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____655 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____656 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____673 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____686 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____693 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____708 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____731 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____758 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____771 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____788,m) ->
        let uu____830 = FStar_ST.op_Bang m in
        (match uu____830 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____877 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____882 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let (uvar_to_string :FStar_Syntax_Syntax.uvar -> Prims.string)=
  fun u  ->
    let uu____893 = FStar_Options.hide_uvar_nums () in
    if uu____893
    then "?"
    else
      (let uu____895 =
         let uu____896 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____896 FStar_Util.string_of_int in
       Prims.strcat "?" uu____895)
let (version_to_string :FStar_Syntax_Syntax.version -> Prims.string)=
  fun v1  ->
    let uu____901 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____902 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____901 uu____902
let (univ_uvar_to_string :FStar_Syntax_Syntax.universe_uvar -> Prims.string)=
  fun u  ->
    let uu____907 = FStar_Options.hide_uvar_nums () in
    if uu____907
    then "?"
    else
      (let uu____909 =
         let uu____910 =
           let uu____911 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____911 FStar_Util.string_of_int in
         let uu____912 =
           let uu____913 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____913 in
         Prims.strcat uu____910 uu____912 in
       Prims.strcat "?" uu____909)
let rec (int_of_univ
  :Prims.int ->
     FStar_Syntax_Syntax.universe ->
       (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
         FStar_Pervasives_Native.tuple2)=
  fun n1  ->
    fun u  ->
      let uu____932 = FStar_Syntax_Subst.compress_univ u in
      match uu____932 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____942 -> (n1, (FStar_Pervasives_Native.Some u))
let rec (univ_to_string :FStar_Syntax_Syntax.universe -> Prims.string)=
  fun u  ->
    let uu____949 =
      let uu____950 = FStar_Options.ugly () in Prims.op_Negation uu____950 in
    if uu____949
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____954 = FStar_Syntax_Subst.compress_univ u in
       match uu____954 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____966 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____966
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____968 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____968 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____982 = univ_to_string u2 in
                let uu____983 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____982 uu____983)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____987 =
             let uu____988 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____988 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____987
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let (univs_to_string
  :FStar_Syntax_Syntax.universe Prims.list -> Prims.string)=
  fun us  ->
    let uu____1001 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____1001 (FStar_String.concat ", ")
let (univ_names_to_string :FStar_Ident.ident Prims.list -> Prims.string)=
  fun us  ->
    let uu____1014 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____1014 (FStar_String.concat ", ")
let (qual_to_string :FStar_Syntax_Syntax.qualifier -> Prims.string)=
  fun uu___203_1024  ->
    match uu___203_1024 with
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
        let uu____1026 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____1026
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1029 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____1029
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1040 =
          let uu____1041 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1041 in
        let uu____1044 =
          let uu____1045 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1045 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1040 uu____1044
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1064 =
          let uu____1065 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1065 in
        let uu____1068 =
          let uu____1069 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1069 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1064 uu____1068
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1079 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1079
    | FStar_Syntax_Syntax.ExceptionConstructor  -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect  -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect  -> "Effect"
    | FStar_Syntax_Syntax.Reifiable  -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str
    | FStar_Syntax_Syntax.OnlyName  -> "OnlyName"
let (quals_to_string
  :FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string)=
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1089 ->
        let uu____1092 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1092 (FStar_String.concat " ")
let (quals_to_string'
  :FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string)=
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1109 ->
        let uu____1112 = quals_to_string quals in Prims.strcat uu____1112 " "
let rec (term_to_string :FStar_Syntax_Syntax.term -> Prims.string)=
  fun x  ->
    let uu____1168 =
      let uu____1169 = FStar_Options.ugly () in Prims.op_Negation uu____1169 in
    if uu____1168
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1175 = FStar_Options.print_implicits () in
         if uu____1175 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1177 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1202,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1238 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1268 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1286  ->
                                 match uu____1286 with
                                 | (t1,uu____1292) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1268
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1238 (FStar_String.concat "\\/") in
           let uu____1297 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1297
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1309 = tag_of_term t in
           let uu____1310 = sli m in
           let uu____1311 = term_to_string t' in
           let uu____1312 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1309 uu____1310
             uu____1311 uu____1312
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1325 = tag_of_term t in
           let uu____1326 = term_to_string t' in
           let uu____1327 = sli m0 in
           let uu____1328 = sli m1 in
           let uu____1329 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1325
             uu____1326 uu____1327 uu____1328 uu____1329
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1331,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____1345 = FStar_Range.string_of_range r in
           let uu____1346 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1345
             uu____1346
       | FStar_Syntax_Syntax.Tm_meta (t,uu____1348) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1354 = db_to_string x3 in
           let uu____1355 =
             let uu____1356 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1356 in
           Prims.strcat uu____1354 uu____1355
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1360) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1387 = FStar_Options.print_universes () in
           if uu____1387
           then
             let uu____1388 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1388
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1408 = binders_to_string " -> " bs in
           let uu____1409 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1408 uu____1409
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1434 = binders_to_string " " bs in
                let uu____1435 = term_to_string t2 in
                let uu____1436 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1440 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1440) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1434 uu____1435
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1436
            | uu____1443 ->
                let uu____1446 = binders_to_string " " bs in
                let uu____1447 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1446 uu____1447)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1454 = bv_to_string xt in
           let uu____1455 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1458 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1454 uu____1455 uu____1458
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1483 = term_to_string t in
           let uu____1484 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1483 uu____1484
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1503 = lbs_to_string [] lbs in
           let uu____1504 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1503 uu____1504
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1565 =
                   let uu____1566 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1566
                     (FStar_Util.dflt "default") in
                 let uu____1571 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1565 uu____1571
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1587 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1587 in
           let uu____1588 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1588 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1627 = term_to_string head1 in
           let uu____1628 =
             let uu____1629 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1665  ->
                       match uu____1665 with
                       | (p,wopt,e) ->
                           let uu____1681 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1682 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1684 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1684 in
                           let uu____1685 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1681
                             uu____1682 uu____1685)) in
             FStar_Util.concat_l "\n\t|" uu____1629 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1627 uu____1628
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1692 = FStar_Options.print_universes () in
           if uu____1692
           then
             let uu____1693 = term_to_string t in
             let uu____1694 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1693 uu____1694
           else term_to_string t
       | uu____1696 -> tag_of_term x2)
and (pat_to_string :FStar_Syntax_Syntax.pat -> Prims.string)=
  fun x  ->
    let uu____1698 =
      let uu____1699 = FStar_Options.ugly () in Prims.op_Negation uu____1699 in
    if uu____1698
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1721 = fv_to_string l in
           let uu____1722 =
             let uu____1723 =
               FStar_List.map
                 (fun uu____1734  ->
                    match uu____1734 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1723 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1721 uu____1722
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1746) ->
           let uu____1751 = FStar_Options.print_bound_var_types () in
           if uu____1751
           then
             let uu____1752 = bv_to_string x1 in
             let uu____1753 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1752 uu____1753
           else
             (let uu____1755 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1755)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1757 = FStar_Options.print_bound_var_types () in
           if uu____1757
           then
             let uu____1758 = bv_to_string x1 in
             let uu____1759 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1758 uu____1759
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1763 = FStar_Options.print_real_names () in
           if uu____1763
           then
             let uu____1764 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1764
           else "_")
and (lbs_to_string
  :FStar_Syntax_Syntax.qualifier Prims.list ->
     (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
       FStar_Pervasives_Native.tuple2 -> Prims.string)=
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1783 = FStar_Options.print_universes () in
        if uu____1783
        then
          let uu____1790 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1808 =
                      let uu____1813 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1813 in
                    match uu____1808 with
                    | (us,td) ->
                        let uu____1816 =
                          let uu____1825 =
                            let uu____1826 = FStar_Syntax_Subst.compress td in
                            uu____1826.FStar_Syntax_Syntax.n in
                          match uu____1825 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1837,(t,uu____1839)::(d,uu____1841)::[])
                              -> (t, d)
                          | uu____1884 -> failwith "Impossibe" in
                        (match uu____1816 with
                         | (t,d) ->
                             let uu___210_1903 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___210_1903.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___210_1903.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1790)
        else lbs in
      let uu____1909 = quals_to_string' quals in
      let uu____1910 =
        let uu____1911 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1926 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1927 =
                    let uu____1928 = FStar_Options.print_universes () in
                    if uu____1928
                    then
                      let uu____1929 =
                        let uu____1930 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1930 ">" in
                      Prims.strcat "<" uu____1929
                    else "" in
                  let uu____1932 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1933 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1926 uu____1927
                    uu____1932 uu____1933)) in
        FStar_Util.concat_l "\n and " uu____1911 in
      FStar_Util.format3 "%slet %s %s" uu____1909
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1910
and (lcomp_to_string :FStar_Syntax_Syntax.lcomp -> Prims.string)=
  fun lc  ->
    let uu____1940 = FStar_Options.print_effect_args () in
    if uu____1940
    then
      let uu____1941 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1941
    else
      (let uu____1943 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1944 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1943 uu____1944)
and (imp_to_string
  :Prims.string ->
     FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
       Prims.string)=
  fun s  ->
    fun uu___204_1946  ->
      match uu___204_1946 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1949 -> s
and (binder_to_string'
  :Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string)=
  fun is_arrow  ->
    fun b  ->
      let uu____1954 =
        let uu____1955 = FStar_Options.ugly () in
        Prims.op_Negation uu____1955 in
      if uu____1954
      then
        let uu____1956 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1956 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1962 = b in
         match uu____1962 with
         | (a,imp) ->
             let uu____1965 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1965
             then
               let uu____1966 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1966
             else
               (let uu____1968 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1970 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1970) in
                if uu____1968
                then
                  let uu____1971 = nm_to_string a in
                  imp_to_string uu____1971 imp
                else
                  (let uu____1973 =
                     let uu____1974 = nm_to_string a in
                     let uu____1975 =
                       let uu____1976 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1976 in
                     Prims.strcat uu____1974 uu____1975 in
                   imp_to_string uu____1973 imp)))
and (binder_to_string :FStar_Syntax_Syntax.binder -> Prims.string)=
  fun b  -> binder_to_string' false b
and (arrow_binder_to_string :FStar_Syntax_Syntax.binder -> Prims.string)=
  fun b  -> binder_to_string' true b
and (binders_to_string
  :Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string)=
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1982 = FStar_Options.print_implicits () in
        if uu____1982 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1984 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1984 (FStar_String.concat sep)
      else
        (let uu____1992 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1992 (FStar_String.concat sep))
and (arg_to_string
  :(FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                               FStar_Pervasives_Native.option)
     FStar_Pervasives_Native.tuple2 -> Prims.string)=
  fun uu___205_1999  ->
    match uu___205_1999 with
    | (a,imp) ->
        let uu____2012 = term_to_string a in imp_to_string uu____2012 imp
and (args_to_string :FStar_Syntax_Syntax.args -> Prims.string)=
  fun args  ->
    let args1 =
      let uu____2015 = FStar_Options.print_implicits () in
      if uu____2015 then args else filter_imp args in
    let uu____2019 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____2019 (FStar_String.concat " ")
and (comp_to_string :FStar_Syntax_Syntax.comp -> Prims.string)=
  fun c  ->
    let uu____2033 =
      let uu____2034 = FStar_Options.ugly () in Prims.op_Negation uu____2034 in
    if uu____2033
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2048 =
             let uu____2049 = FStar_Syntax_Subst.compress t in
             uu____2049.FStar_Syntax_Syntax.n in
           (match uu____2048 with
            | FStar_Syntax_Syntax.Tm_type uu____2052 when
                let uu____2053 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2053 -> term_to_string t
            | uu____2054 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2056 = univ_to_string u in
                     let uu____2057 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2056 uu____2057
                 | uu____2058 ->
                     let uu____2061 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2061))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2072 =
             let uu____2073 = FStar_Syntax_Subst.compress t in
             uu____2073.FStar_Syntax_Syntax.n in
           (match uu____2072 with
            | FStar_Syntax_Syntax.Tm_type uu____2076 when
                let uu____2077 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2077 -> term_to_string t
            | uu____2078 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2080 = univ_to_string u in
                     let uu____2081 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2080 uu____2081
                 | uu____2082 ->
                     let uu____2085 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2085))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2088 = FStar_Options.print_effect_args () in
             if uu____2088
             then
               let uu____2089 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2090 =
                 let uu____2091 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2091 (FStar_String.concat ", ") in
               let uu____2098 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2099 =
                 let uu____2100 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2100 (FStar_String.concat ", ") in
               let uu____2121 =
                 let uu____2122 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2122 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2089
                 uu____2090 uu____2098 uu____2099 uu____2121
             else
               (let uu____2132 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___206_2136  ->
                           match uu___206_2136 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2137 -> false)))
                    &&
                    (let uu____2139 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2139) in
                if uu____2132
                then
                  let uu____2140 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2140
                else
                  (let uu____2142 =
                     ((let uu____2145 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2145) &&
                        (let uu____2147 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2147))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2142
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2149 =
                        (let uu____2152 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2152) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___207_2156  ->
                                   match uu___207_2156 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2157 -> false))) in
                      if uu____2149
                      then
                        let uu____2158 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2158
                      else
                        (let uu____2160 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2161 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2160 uu____2161)))) in
           let dec =
             let uu____2163 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___208_2173  ->
                       match uu___208_2173 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2179 =
                             let uu____2180 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2180 in
                           [uu____2179]
                       | uu____2181 -> [])) in
             FStar_All.pipe_right uu____2163 (FStar_String.concat " ") in
           FStar_Util.format2 "%s%s" basic dec)
and (cflags_to_string :FStar_Syntax_Syntax.cflags -> Prims.string)=
  fun c  ->
    match c with
    | FStar_Syntax_Syntax.TOTAL  -> "total"
    | FStar_Syntax_Syntax.MLEFFECT  -> "ml"
    | FStar_Syntax_Syntax.RETURN  -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN  -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL  -> "sometrivial"
    | FStar_Syntax_Syntax.LEMMA  -> "lemma"
    | FStar_Syntax_Syntax.CPS  -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____2185 -> ""
and (formula_to_string
  :FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string)=
  fun phi  -> term_to_string phi
let (binder_to_json :FStar_Syntax_Syntax.binder -> FStar_Util.json)=
  fun b  ->
    let uu____2195 = b in
    match uu____2195 with
    | (a,imp) ->
        let n1 =
          let uu____2199 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2199
          then FStar_Util.JsonNull
          else
            (let uu____2201 =
               let uu____2202 = nm_to_string a in
               imp_to_string uu____2202 imp in
             FStar_Util.JsonStr uu____2201) in
        let t =
          let uu____2204 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2204 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let (binders_to_json :FStar_Syntax_Syntax.binders -> FStar_Util.json)=
  fun bs  ->
    let uu____2221 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2221
let (enclose_universes :Prims.string -> Prims.string)=
  fun s  ->
    let uu____2228 = FStar_Options.print_universes () in
    if uu____2228 then Prims.strcat "<" (Prims.strcat s ">") else ""
let (tscheme_to_string :FStar_Syntax_Syntax.tscheme -> Prims.string)=
  fun s  ->
    let uu____2234 =
      let uu____2235 = FStar_Options.ugly () in Prims.op_Negation uu____2235 in
    if uu____2234
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2239 = s in
       match uu____2239 with
       | (us,t) ->
           let uu____2246 =
             let uu____2247 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2247 in
           let uu____2248 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2246 uu____2248)
let (action_to_string :FStar_Syntax_Syntax.action -> Prims.string)=
  fun a  ->
    let uu____2253 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2254 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2255 =
      let uu____2256 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2256 in
    let uu____2257 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2258 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2253 uu____2254 uu____2255
      uu____2257 uu____2258
let (eff_decl_to_string'
  :Prims.bool ->
     FStar_Range.range ->
       FStar_Syntax_Syntax.qualifier Prims.list ->
         FStar_Syntax_Syntax.eff_decl -> Prims.string)=
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____2279 =
            let uu____2280 = FStar_Options.ugly () in
            Prims.op_Negation uu____2280 in
          if uu____2279
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2292 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2292 (FStar_String.concat ",\n\t") in
             let uu____2301 =
               let uu____2304 =
                 let uu____2307 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2308 =
                   let uu____2311 =
                     let uu____2312 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2312 in
                   let uu____2313 =
                     let uu____2316 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2317 =
                       let uu____2320 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2321 =
                         let uu____2324 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2325 =
                           let uu____2328 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2329 =
                             let uu____2332 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2333 =
                               let uu____2336 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2337 =
                                 let uu____2340 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2341 =
                                   let uu____2344 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2345 =
                                     let uu____2348 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2349 =
                                       let uu____2352 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2353 =
                                         let uu____2356 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2357 =
                                           let uu____2360 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2361 =
                                             let uu____2364 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2365 =
                                               let uu____2368 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2369 =
                                                 let uu____2372 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2373 =
                                                   let uu____2376 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2376] in
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
                       uu____2320 :: uu____2321 in
                     uu____2316 :: uu____2317 in
                   uu____2311 :: uu____2313 in
                 uu____2307 :: uu____2308 in
               (if for_free then "_for_free " else "") :: uu____2304 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2301)
let (eff_decl_to_string
  :Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string)=
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec (sigelt_to_string :FStar_Syntax_Syntax.sigelt -> Prims.string)=
  fun x  ->
    let uu____2390 =
      let uu____2391 = FStar_Options.ugly () in Prims.op_Negation uu____2391 in
    if uu____2390
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2397 -> ""
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
           (lid,univs1,tps,k,uu____2407,uu____2408) ->
           let uu____2417 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2418 = binders_to_string " " tps in
           let uu____2419 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2417
             lid.FStar_Ident.str uu____2418 uu____2419
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2423,uu____2424,uu____2425) ->
           let uu____2430 = FStar_Options.print_universes () in
           if uu____2430
           then
             let uu____2431 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2431 with
              | (univs2,t1) ->
                  let uu____2438 = univ_names_to_string univs2 in
                  let uu____2439 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2438
                    lid.FStar_Ident.str uu____2439)
           else
             (let uu____2441 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2441)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2445 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2445 with
            | (univs2,t1) ->
                let uu____2452 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2453 =
                  let uu____2454 = FStar_Options.print_universes () in
                  if uu____2454
                  then
                    let uu____2455 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2455
                  else "" in
                let uu____2457 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2452
                  lid.FStar_Ident.str uu____2453 uu____2457)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2459,f) ->
           let uu____2461 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2461
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2463) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2469 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2469
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2471) ->
           let uu____2480 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2480 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2498) -> lift_wp
             | (uu____2505,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2513 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2513 with
            | (us,t) ->
                let uu____2524 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2525 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2526 = univ_names_to_string us in
                let uu____2527 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2524
                  uu____2525 uu____2526 uu____2527)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2537 = FStar_Options.print_universes () in
           if uu____2537
           then
             let uu____2538 =
               let uu____2543 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2543 in
             (match uu____2538 with
              | (univs2,t) ->
                  let uu____2546 =
                    let uu____2559 =
                      let uu____2560 = FStar_Syntax_Subst.compress t in
                      uu____2560.FStar_Syntax_Syntax.n in
                    match uu____2559 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2601 -> failwith "impossible" in
                  (match uu____2546 with
                   | (tps1,c1) ->
                       let uu____2632 = sli l in
                       let uu____2633 = univ_names_to_string univs2 in
                       let uu____2634 = binders_to_string " " tps1 in
                       let uu____2635 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2632
                         uu____2633 uu____2634 uu____2635))
           else
             (let uu____2637 = sli l in
              let uu____2638 = binders_to_string " " tps in
              let uu____2639 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2637 uu____2638
                uu____2639))
let (format_error :FStar_Range.range -> Prims.string -> Prims.string)=
  fun r  ->
    fun msg  ->
      let uu____2648 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2648 msg
let rec (sigelt_to_string_short :FStar_Syntax_Syntax.sigelt -> Prims.string)=
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2653,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2655;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2657;
                       FStar_Syntax_Syntax.lbdef = uu____2658;_}::[]),uu____2659)
        ->
        let uu____2682 = lbname_to_string lb in
        let uu____2683 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2682 uu____2683
    | uu____2684 ->
        let uu____2685 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2685 (FStar_String.concat ", ")
let rec (modul_to_string :FStar_Syntax_Syntax.modul -> Prims.string)=
  fun m  ->
    let uu____2700 = sli m.FStar_Syntax_Syntax.name in
    let uu____2701 =
      let uu____2702 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2702 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2700 uu____2701
let (subst_elt_to_string :FStar_Syntax_Syntax.subst_elt -> Prims.string)=
  fun uu___209_2710  ->
    match uu___209_2710 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2713 = FStar_Util.string_of_int i in
        let uu____2714 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2713 uu____2714
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2717 = bv_to_string x in
        let uu____2718 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2717 uu____2718
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2725 = bv_to_string x in
        let uu____2726 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2725 uu____2726
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2729 = FStar_Util.string_of_int i in
        let uu____2730 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2729 uu____2730
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2733 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2733
let (subst_to_string :FStar_Syntax_Syntax.subst_t -> Prims.string)=
  fun s  ->
    let uu____2738 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2738 (FStar_String.concat "; ")
let (abs_ascription_to_string
  :(FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
     FStar_Pervasives_Native.option -> Prims.string)=
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
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string=
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "[";
           (let uu____2810 = f x in
            FStar_Util.string_builder_append strb uu____2810);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2817 = f x1 in
                 FStar_Util.string_builder_append strb uu____2817)) xs;
           FStar_Util.string_builder_append strb "]";
           FStar_Util.string_of_string_builder strb)
let set_to_string :
  'a . ('a -> Prims.string) -> 'a FStar_Util.set -> Prims.string=
  fun f  ->
    fun s  ->
      let elts = FStar_Util.set_elements s in
      match elts with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "{";
           (let uu____2853 = f x in
            FStar_Util.string_builder_append strb uu____2853);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2860 = f x1 in
                 FStar_Util.string_builder_append strb uu____2860)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)