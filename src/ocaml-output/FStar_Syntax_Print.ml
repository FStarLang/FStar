open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___0_5  ->
    match uu___0_5 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____9 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____9
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____14 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____14
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____18 =
          let uu____20 = delta_depth_to_string d  in
          Prims.op_Hat uu____20 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____18
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____40 = FStar_Options.print_real_names ()  in
    if uu____40
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____95 =
      let uu____97 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____97  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____95
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____117 = FStar_Options.print_real_names ()  in
    if uu____117
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____140 =
      let uu____142 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____142  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____140
  
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
  fun ps  ->
    fun f  ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____599 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____635 -> failwith "get_lid"
  
let (is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
  
let (is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
  
let (quants : (FStar_Ident.lident * Prims.string) Prims.list) =
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")] 
type exp = FStar_Syntax_Syntax.term
let (is_b2t : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  -> is_prim_op [FStar_Parser_Const.b2t_lid] t 
let (is_quant : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t
  
let (is_ite : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  -> is_prim_op [FStar_Parser_Const.ite_lid] t 
let (is_lex_cons : exp -> Prims.bool) =
  fun f  -> is_prim_op [FStar_Parser_Const.lexcons_lid] f 
let (is_lex_top : exp -> Prims.bool) =
  fun f  -> is_prim_op [FStar_Parser_Const.lextop_lid] f 
let is_inr :
  'Auu____882 'Auu____883 .
    ('Auu____882,'Auu____883) FStar_Util.either -> Prims.bool
  =
  fun uu___1_893  ->
    match uu___1_893 with
    | FStar_Util.Inl uu____898 -> false
    | FStar_Util.Inr uu____900 -> true
  
let filter_imp :
  'Auu____907 .
    ('Auu____907 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____907 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___2_962  ->
            match uu___2_962 with
            | (uu____970,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____981,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____982)) -> false
            | (uu____987,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____988)) -> false
            | uu____998 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____1028 =
      let uu____1029 = FStar_Syntax_Subst.compress e  in
      uu____1029.FStar_Syntax_Syntax.n  in
    match uu____1028 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____1142 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____1142
        then
          let uu____1159 =
            let uu____1168 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____1168  in
          (match uu____1159 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____1203 =
                 let uu____1210 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____1210 :: xs  in
               FStar_Pervasives_Native.Some uu____1203
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____1254 ->
        let uu____1255 = is_lex_top e  in
        if uu____1255
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____1319 = f hd1  in if uu____1319 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____1367 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____1367
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____1426 = get_lid e  in find_lid uu____1426 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____1454 = get_lid e  in find_lid uu____1454 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____1482 = get_lid t  in find_lid uu____1482 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___3_1504  ->
    match uu___3_1504 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____1543 = FStar_Options.hide_uvar_nums ()  in
    if uu____1543
    then "?"
    else
      (let uu____1550 =
         let uu____1552 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____1552 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____1550)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____1568 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____1570 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____1568 uu____1570
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____1600 = FStar_Options.hide_uvar_nums ()  in
    if uu____1600
    then "?"
    else
      (let uu____1607 =
         let uu____1609 =
           let uu____1611 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____1611 FStar_Util.string_of_int  in
         let uu____1615 =
           let uu____1617 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.op_Hat ":" uu____1617  in
         Prims.op_Hat uu____1609 uu____1615  in
       Prims.op_Hat "?" uu____1607)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____1647 = FStar_Syntax_Subst.compress_univ u  in
      match uu____1647 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____1660 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____1671 = FStar_Syntax_Subst.compress_univ u  in
    match uu____1671 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____1684 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____1684
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____1693 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____1693
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1698 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____1698 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____1719 = univ_to_string u2  in
             let uu____1721 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____1719 uu____1721)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____1727 =
          let uu____1729 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____1729 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____1727
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____1748 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____1748 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____1765 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____1765 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___4_1787  ->
    match uu___4_1787 with
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
        let uu____1807 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____1807
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1824 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____1824
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1845 =
          let uu____1847 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1847  in
        let uu____1848 =
          let uu____1850 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1850 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____1845 uu____1848
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1888 =
          let uu____1890 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1890  in
        let uu____1891 =
          let uu____1893 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1893 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1888 uu____1891
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1918 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____1918
    | FStar_Syntax_Syntax.ExceptionConstructor  -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect  -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect  -> "Effect"
    | FStar_Syntax_Syntax.Reifiable  -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str
    | FStar_Syntax_Syntax.OnlyName  -> "OnlyName"
  
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1945 ->
        let uu____1948 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____1948 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1976 ->
        let uu____1979 = quals_to_string quals  in
        Prims.op_Hat uu____1979 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____2238 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____2238
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____2247 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____2247
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____2254 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____2254
    | FStar_Syntax_Syntax.Tm_uinst uu____2261 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____2273 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____2275 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____2277,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____2278;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____2311,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____2312;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____2345 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____2381 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____2406 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____2423 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____2449 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____2488 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____2536 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____2562 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____2584,m) ->
        let uu____2638 = FStar_ST.op_Bang m  in
        (match uu____2638 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____2690 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____2704,m) ->
        let uu____2718 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____2718
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____2722 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____2733 =
      let uu____2735 = FStar_Options.ugly ()  in Prims.op_Negation uu____2735
       in
    if uu____2733
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____2771 = FStar_Options.print_implicits ()  in
         if uu____2771 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2783 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____2816,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____2858,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____2860;
             FStar_Syntax_Syntax.rng = uu____2861;_}
           ->
           let uu____2884 =
             let uu____2886 =
               let uu____2888 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____2888  in
             Prims.op_Hat uu____2886 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____2884
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____2910 =
             let uu____2912 =
               let uu____2914 =
                 let uu____2923 =
                   let uu____2940 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____2940  in
                 uu____2923 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____2914  in
             Prims.op_Hat uu____2912 "]"  in
           Prims.op_Hat "[lazy:" uu____2910
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____3062 =
                  match uu____3062 with
                  | (bv,t) ->
                      let uu____3097 = bv_to_string bv  in
                      let uu____3099 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____3097 uu____3099
                   in
                let uu____3102 = term_to_string tm  in
                let uu____3104 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____3102 uu____3104
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____3122 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____3122)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_pattern (uu____3126,ps)) ->
           let pats =
             let uu____3190 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____3239 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____3272  ->
                                 match uu____3272 with
                                 | (t1,uu____3285) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____3239
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____3190 (FStar_String.concat "\\/")  in
           let uu____3308 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____3308
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____3346 = tag_of_term t  in
           let uu____3348 = sli m  in
           let uu____3350 = term_to_string t'  in
           let uu____3352 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____3346 uu____3348
             uu____3350 uu____3352
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____3399 = tag_of_term t  in
           let uu____3401 = term_to_string t'  in
           let uu____3403 = sli m0  in
           let uu____3405 = sli m1  in
           let uu____3407 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____3399
             uu____3401 uu____3403 uu____3405 uu____3407
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____3430 = FStar_Range.string_of_range r  in
           let uu____3432 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____3430
             uu____3432
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____3453 = lid_to_string l  in
           let uu____3455 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____3457 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____3453 uu____3455
             uu____3457
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____3461) ->
           let uu____3474 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____3474
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____3483 = db_to_string x3  in
           let uu____3485 =
             let uu____3487 =
               let uu____3489 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____3489 ")"  in
             Prims.op_Hat ":(" uu____3487  in
           Prims.op_Hat uu____3483 uu____3485
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____3504)) ->
           let uu____3535 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____3535
           then ctx_uvar_to_string u
           else
             (let uu____3541 =
                let uu____3543 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____3543  in
              Prims.op_Hat "?" uu____3541)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____3582 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____3582
           then
             let uu____3586 = ctx_uvar_to_string u  in
             let uu____3588 =
               let uu____3590 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____3590 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____3586 uu____3588
           else
             (let uu____3609 =
                let uu____3611 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____3611  in
              Prims.op_Hat "?" uu____3609)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____3618 = FStar_Options.print_universes ()  in
           if uu____3618
           then
             let uu____3622 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____3622
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____3668 = binders_to_string " -> " bs  in
           let uu____3671 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____3668 uu____3671
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____3749 = binders_to_string " " bs  in
                let uu____3752 = term_to_string t2  in
                let uu____3754 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____3767 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____3767)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____3749 uu____3752
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____3754
            | uu____3783 ->
                let uu____3793 = binders_to_string " " bs  in
                let uu____3796 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____3793 uu____3796)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____3823 = bv_to_string xt  in
           let uu____3825 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____3832 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____3823 uu____3825 uu____3832
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____3884 = term_to_string t  in
           let uu____3886 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____3884 uu____3886
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____3931 = lbs_to_string [] lbs  in
           let uu____3933 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____3931 uu____3933
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____4062 =
                   let uu____4064 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____4064
                     (FStar_Util.dflt "default")
                    in
                 let uu____4079 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____4062 uu____4079
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____4124 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____4124
              in
           let uu____4127 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____4127 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____4198 = term_to_string head1  in
           let uu____4200 =
             let uu____4202 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____4251  ->
                       match uu____4251 with
                       | (p,wopt,e) ->
                           let uu____4292 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____4295 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____4312 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____4312
                              in
                           let uu____4320 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____4292
                             uu____4295 uu____4320))
                in
             FStar_Util.concat_l "\n\t|" uu____4202  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____4198 uu____4200
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____4344 = FStar_Options.print_universes ()  in
           if uu____4344
           then
             let uu____4348 = term_to_string t  in
             let uu____4350 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____4348 uu____4350
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____4365 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____4368 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____4370 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____4365 uu____4368
      uu____4370

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_4373  ->
    match uu___5_4373 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____4389 = FStar_Util.string_of_int i  in
        let uu____4391 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____4389 uu____4391
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____4408 = bv_to_string x  in
        let uu____4410 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____4408 uu____4410
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____4437 = bv_to_string x  in
        let uu____4439 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____4437 uu____4439
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____4446 = FStar_Util.string_of_int i  in
        let uu____4448 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____4446 uu____4448
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____4459 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____4459

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____4463 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____4463 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____4479 =
      let uu____4481 = FStar_Options.ugly ()  in Prims.op_Negation uu____4481
       in
    if uu____4479
    then
      let e =
        let uu____4490 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____4490  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____4536 = fv_to_string l  in
           let uu____4538 =
             let uu____4540 =
               FStar_List.map
                 (fun uu____4554  ->
                    match uu____4554 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____4540 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____4536 uu____4538
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____4579) ->
           let uu____4602 = FStar_Options.print_bound_var_types ()  in
           if uu____4602
           then
             let uu____4606 = bv_to_string x1  in
             let uu____4608 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____4606 uu____4608
           else
             (let uu____4613 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____4613)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____4622 = FStar_Options.print_bound_var_types ()  in
           if uu____4622
           then
             let uu____4626 = bv_to_string x1  in
             let uu____4628 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____4626 uu____4628
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____4640 = FStar_Options.print_bound_var_types ()  in
           if uu____4640
           then
             let uu____4644 = bv_to_string x1  in
             let uu____4646 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____4644 uu____4646
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____4655 = quals_to_string' quals  in
      let uu____4657 =
        let uu____4659 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____4707 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____4709 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____4711 =
                    let uu____4713 = FStar_Options.print_universes ()  in
                    if uu____4713
                    then
                      let uu____4717 =
                        let uu____4719 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____4719 ">"  in
                      Prims.op_Hat "<" uu____4717
                    else ""  in
                  let uu____4726 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____4728 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____4707
                    uu____4709 uu____4711 uu____4726 uu____4728))
           in
        FStar_Util.concat_l "\n and " uu____4659  in
      FStar_Util.format3 "%slet %s %s" uu____4655
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____4657

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_4754  ->
    match uu___6_4754 with
    | [] -> ""
    | tms ->
        let uu____4774 =
          let uu____4776 =
            FStar_List.map
              (fun t  ->
                 let uu____4792 = term_to_string t  in paren uu____4792) tms
             in
          FStar_All.pipe_right uu____4776 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____4774

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____4809 = FStar_Options.print_effect_args ()  in
    if uu____4809
    then
      let uu____4813 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____4813
    else
      (let uu____4824 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____4826 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____4824 uu____4826)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___7_4830  ->
      match uu___7_4830 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.op_Hat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.op_Hat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.op_Hat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.op_Hat "[|" (Prims.op_Hat s "|]")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____4856 =
            let uu____4858 = term_to_string t  in
            Prims.op_Hat uu____4858 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____4856
      | FStar_Pervasives_Native.None  -> s

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq  -> aqual_to_string' "" aq

and (imp_to_string :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  = fun s  -> fun aq  -> aqual_to_string' s aq

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____4883 =
        let uu____4885 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____4885  in
      if uu____4883
      then
        let uu____4889 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____4889 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____4916 = b  in
         match uu____4916 with
         | (a,imp) ->
             let uu____4945 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____4945
             then
               let uu____4949 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat "_:" uu____4949
             else
               (let uu____4954 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____4957 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____4957)
                   in
                if uu____4954
                then
                  let uu____4961 = nm_to_string a  in
                  imp_to_string uu____4961 imp
                else
                  (let uu____4965 =
                     let uu____4967 = nm_to_string a  in
                     let uu____4969 =
                       let uu____4971 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____4971  in
                     Prims.op_Hat uu____4967 uu____4969  in
                   imp_to_string uu____4965 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  = fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____4995 = FStar_Options.print_implicits ()  in
        if uu____4995 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____5011 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____5011 (FStar_String.concat sep)
      else
        (let uu____5049 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____5049 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_5063  ->
    match uu___8_5063 with
    | (a,imp) ->
        let uu____5089 = term_to_string a  in imp_to_string uu____5089 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____5105 = FStar_Options.print_implicits ()  in
      if uu____5105 then args else filter_imp args  in
    let uu____5128 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____5128 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____5169 = FStar_Options.ugly ()  in
      if uu____5169
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____5190 =
      let uu____5192 = FStar_Options.ugly ()  in Prims.op_Negation uu____5192
       in
    if uu____5190
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____5227 =
             let uu____5228 = FStar_Syntax_Subst.compress t  in
             uu____5228.FStar_Syntax_Syntax.n  in
           (match uu____5227 with
            | FStar_Syntax_Syntax.Tm_type uu____5240 when
                let uu____5241 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____5241 -> term_to_string t
            | uu____5243 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____5246 = univ_to_string u  in
                     let uu____5248 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____5246 uu____5248
                 | uu____5251 ->
                     let uu____5254 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____5254))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____5275 =
             let uu____5276 = FStar_Syntax_Subst.compress t  in
             uu____5276.FStar_Syntax_Syntax.n  in
           (match uu____5275 with
            | FStar_Syntax_Syntax.Tm_type uu____5288 when
                let uu____5289 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____5289 -> term_to_string t
            | uu____5291 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____5294 = univ_to_string u  in
                     let uu____5296 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____5294 uu____5296
                 | uu____5299 ->
                     let uu____5302 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____5302))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____5313 = FStar_Options.print_effect_args ()  in
             if uu____5313
             then
               let uu____5317 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____5319 =
                 let uu____5321 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____5321 (FStar_String.concat ", ")
                  in
               let uu____5336 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____5338 =
                 let uu____5340 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____5340 (FStar_String.concat ", ")
                  in
               let uu____5375 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____5317
                 uu____5319 uu____5336 uu____5338 uu____5375
             else
               (let uu____5380 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_5386  ->
                           match uu___9_5386 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____5389 -> false)))
                    &&
                    (let uu____5392 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____5392)
                   in
                if uu____5380
                then
                  let uu____5396 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____5396
                else
                  (let uu____5401 =
                     ((let uu____5405 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____5405) &&
                        (let uu____5408 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____5408))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____5401
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____5414 =
                        (let uu____5418 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____5418) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_5424  ->
                                   match uu___10_5424 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____5427 -> false)))
                         in
                      if uu____5414
                      then
                        let uu____5431 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____5431
                      else
                        (let uu____5436 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____5438 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____5436 uu____5438))))
              in
           let dec =
             let uu____5443 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_5456  ->
                       match uu___11_5456 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____5467 =
                             let uu____5469 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____5469
                              in
                           [uu____5467]
                       | uu____5474 -> []))
                in
             FStar_All.pipe_right uu____5443 (FStar_String.concat " ")  in
           FStar_Util.format2 "%s%s" basic dec)

and (cflag_to_string : FStar_Syntax_Syntax.cflag -> Prims.string) =
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
    | FStar_Syntax_Syntax.DECREASES uu____5493 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_5511  ->
    match uu___12_5511 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____5513,ps) ->
        let pats =
          let uu____5565 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____5614 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____5647  ->
                              match uu____5647 with
                              | (t,uu____5660) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____5614
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____5565 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____5689 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____5689
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____5694) ->
        let uu____5699 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____5699
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____5726 = sli m  in
        let uu____5728 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____5726 uu____5728
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____5762 = sli m  in
        let uu____5764 = sli m'  in
        let uu____5766 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____5762
          uu____5764 uu____5766

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____5789 = FStar_Options.ugly ()  in
      if uu____5789
      then term_to_string x
      else
        (let e = FStar_Syntax_Resugar.resugar_term' env x  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)
  
let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env  ->
    fun b  ->
      let uu____5816 = b  in
      match uu____5816 with
      | (a,imp) ->
          let n1 =
            let uu____5834 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____5834
            then FStar_Util.JsonNull
            else
              (let uu____5839 =
                 let uu____5841 = nm_to_string a  in
                 imp_to_string uu____5841 imp  in
               FStar_Util.JsonStr uu____5839)
             in
          let t =
            let uu____5844 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____5844  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____5876 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____5876
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____5899 = FStar_Options.print_universes ()  in
    if uu____5899 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____5915 =
      let uu____5917 = FStar_Options.ugly ()  in Prims.op_Negation uu____5917
       in
    if uu____5915
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____5937 = s  in
       match uu____5937 with
       | (us,t) ->
           let uu____5961 =
             let uu____5963 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____5963  in
           let uu____5967 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____5961 uu____5967)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____5997 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____5999 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____6002 =
      let uu____6004 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____6004  in
    let uu____6008 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____6010 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____5997 uu____5999 uu____6002
      uu____6008 uu____6010
  
let (eff_decl_to_string' :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string)
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____6081 =
            let uu____6083 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____6083  in
          if uu____6081
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____6134 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____6134 (FStar_String.concat ",\n\t")
                in
             let uu____6169 =
               let uu____6173 =
                 let uu____6177 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____6179 =
                   let uu____6183 =
                     let uu____6185 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____6185  in
                   let uu____6189 =
                     let uu____6193 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____6196 =
                       let uu____6200 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____6202 =
                         let uu____6206 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____6208 =
                           let uu____6212 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____6214 =
                             let uu____6218 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____6220 =
                               let uu____6224 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____6226 =
                                 let uu____6230 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____6232 =
                                   let uu____6236 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____6238 =
                                     let uu____6242 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____6244 =
                                       let uu____6248 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____6250 =
                                         let uu____6254 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____6256 =
                                           let uu____6260 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____6262 =
                                             let uu____6266 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____6268 =
                                               let uu____6272 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____6274 =
                                                 let uu____6278 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____6280 =
                                                   let uu____6284 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____6284]  in
                                                 uu____6278 :: uu____6280  in
                                               uu____6272 :: uu____6274  in
                                             uu____6266 :: uu____6268  in
                                           uu____6260 :: uu____6262  in
                                         uu____6254 :: uu____6256  in
                                       uu____6248 :: uu____6250  in
                                     uu____6242 :: uu____6244  in
                                   uu____6236 :: uu____6238  in
                                 uu____6230 :: uu____6232  in
                               uu____6224 :: uu____6226  in
                             uu____6218 :: uu____6220  in
                           uu____6212 :: uu____6214  in
                         uu____6206 :: uu____6208  in
                       uu____6200 :: uu____6202  in
                     uu____6193 :: uu____6196  in
                   uu____6183 :: uu____6189  in
                 uu____6177 :: uu____6179  in
               (if for_free then "_for_free " else "") :: uu____6173  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____6169)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
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
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.None )) -> "#push-options"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.Some s)) ->
          FStar_Util.format1 "#push-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
          "#pop-options"
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univs1,tps,k,uu____6408,uu____6409) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____6457 = FStar_Options.print_universes ()  in
          if uu____6457
          then
            let uu____6461 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____6461 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____6470,uu____6471,uu____6472) ->
          let uu____6511 = FStar_Options.print_universes ()  in
          if uu____6511
          then
            let uu____6515 = univ_names_to_string univs1  in
            let uu____6517 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____6515
              lid.FStar_Ident.str uu____6517
          else
            (let uu____6522 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____6522)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____6544 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____6546 =
            let uu____6548 = FStar_Options.print_universes ()  in
            if uu____6548
            then
              let uu____6552 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____6552
            else ""  in
          let uu____6558 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____6544
            lid.FStar_Ident.str uu____6546 uu____6558
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____6580 = FStar_Options.print_universes ()  in
          if uu____6580
          then
            let uu____6584 = univ_names_to_string us  in
            let uu____6586 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____6584 uu____6586
          else
            (let uu____6591 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____6591)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____6595) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____6613 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____6613
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____6617) ->
          let uu____6644 =
            let uu____6646 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____6646 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____6644
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____6762) -> lift_wp
            | (uu____6769,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____6777 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____6777 with
           | (us,t) ->
               let uu____6813 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____6815 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____6817 = univ_names_to_string us  in
               let uu____6819 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____6813
                 uu____6815 uu____6817 uu____6819)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____6847 = FStar_Options.print_universes ()  in
          if uu____6847
          then
            let uu____6851 =
              let uu____6860 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____6860  in
            (match uu____6851 with
             | (univs2,t) ->
                 let uu____6899 =
                   let uu____6908 =
                     let uu____6909 = FStar_Syntax_Subst.compress t  in
                     uu____6909.FStar_Syntax_Syntax.n  in
                   match uu____6908 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____6972 -> failwith "impossible"  in
                 (match uu____6899 with
                  | (tps1,c1) ->
                      let uu____6993 = sli l  in
                      let uu____6995 = univ_names_to_string univs2  in
                      let uu____6997 = binders_to_string " " tps1  in
                      let uu____7000 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____6993
                        uu____6995 uu____6997 uu____7000))
          else
            (let uu____7005 = sli l  in
             let uu____7007 = binders_to_string " " tps  in
             let uu____7010 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____7005 uu____7007
               uu____7010)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____7035 =
            let uu____7037 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____7037  in
          let uu____7051 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____7035 uu____7051
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____7059 ->
        let uu____7066 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____7066 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____7083 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____7083 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____7104,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____7106;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____7108;
                       FStar_Syntax_Syntax.lbdef = uu____7109;
                       FStar_Syntax_Syntax.lbattrs = uu____7110;
                       FStar_Syntax_Syntax.lbpos = uu____7111;_}::[]),uu____7112)
        ->
        let uu____7190 = lbname_to_string lb  in
        let uu____7192 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____7190 uu____7192
    | uu____7195 ->
        let uu____7196 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____7196 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____7248 = sli m.FStar_Syntax_Syntax.name  in
    let uu____7250 =
      let uu____7252 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____7252 (FStar_String.concat "\n")  in
    let uu____7267 =
      let uu____7269 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____7269 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____7248
      uu____7250 uu____7267
  
let (abs_ascription_to_string :
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
    FStar_Pervasives_Native.option -> Prims.string)
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder ()  in
    (match ascription with
     | FStar_Pervasives_Native.None  ->
         FStar_Util.string_builder_append strb "None"
     | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____7386 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____7386))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____7423 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____7423)));
    FStar_Util.string_of_string_builder strb
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
           (let uu____7464 = f x  in
            FStar_Util.string_builder_append strb uu____7464);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____7473 = f x1  in
                 FStar_Util.string_builder_append strb uu____7473)) xs;
           FStar_Util.string_builder_append strb "]";
           FStar_Util.string_of_string_builder strb)
  
let set_to_string :
  'a . ('a -> Prims.string) -> 'a FStar_Util.set -> Prims.string =
  fun f  ->
    fun s  ->
      let elts = FStar_Util.set_elements s  in
      match elts with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "{";
           (let uu____7520 = f x  in
            FStar_Util.string_builder_append strb uu____7520);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____7529 = f x1  in
                 FStar_Util.string_builder_append strb uu____7529)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____7561 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____7561
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___13_7584  ->
    match uu___13_7584 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____7600 =
          let uu____7602 =
            let uu____7604 =
              let uu____7606 =
                let uu____7608 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____7608 (FStar_String.concat " ")  in
              Prims.op_Hat uu____7606 ")"  in
            Prims.op_Hat " " uu____7604  in
          Prims.op_Hat h uu____7602  in
        Prims.op_Hat "(" uu____7600
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____7623 =
          let uu____7625 = emb_typ_to_string a  in
          let uu____7627 =
            let uu____7629 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____7629  in
          Prims.op_Hat uu____7625 uu____7627  in
        Prims.op_Hat "(" uu____7623
  