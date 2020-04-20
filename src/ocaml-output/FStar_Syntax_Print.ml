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
    let uu____32 = FStar_Options.print_real_names ()  in
    if uu____32
    then FStar_Ident.string_of_lid l
    else
      (let uu____38 = FStar_Ident.ident_of_lid l  in
       FStar_Ident.text_of_id uu____38)
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____60 = FStar_Ident.text_of_id bv.FStar_Syntax_Syntax.ppname  in
    let uu____62 =
      let uu____64 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____64  in
    Prims.op_Hat uu____60 uu____62
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____74 = FStar_Options.print_real_names ()  in
    if uu____74
    then bv_to_string bv
    else FStar_Ident.text_of_id bv.FStar_Syntax_Syntax.ppname
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____87 = FStar_Ident.text_of_id bv.FStar_Syntax_Syntax.ppname  in
    let uu____89 =
      let uu____91 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____91  in
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
  fun ps  ->
    fun f  ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____313 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____326 -> failwith "get_lid"
  
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
  'uuuuuu429 'uuuuuu430 .
    ('uuuuuu429,'uuuuuu430) FStar_Util.either -> Prims.bool
  =
  fun uu___1_440  ->
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
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___2_509  ->
            match uu___2_509 with
            | (uu____517,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____524,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____525)) -> false
            | (uu____530,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____531)) -> false
            | uu____537 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____555 =
      let uu____556 = FStar_Syntax_Subst.compress e  in
      uu____556.FStar_Syntax_Syntax.n  in
    match uu____555 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____617 =
          (is_lex_cons f) && ((FStar_List.length exps) = (Prims.of_int (2)))
           in
        if uu____617
        then
          let uu____626 =
            let uu____631 = FStar_List.nth exps Prims.int_one  in
            reconstruct_lex uu____631  in
          (match uu____626 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____642 =
                 let uu____645 = FStar_List.nth exps Prims.int_zero  in
                 uu____645 :: xs  in
               FStar_Pervasives_Native.Some uu____642
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____657 ->
        let uu____658 = is_lex_top e  in
        if uu____658
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd::tl ->
          let uu____706 = f hd  in if uu____706 then hd else find f tl
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____738 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____738
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____769 = get_lid e  in find_lid uu____769 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____781 = get_lid e  in find_lid uu____781 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____793 = get_lid t  in find_lid uu____793 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___3_807  ->
    match uu___3_807 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____818 = FStar_Options.hide_uvar_nums ()  in
    if uu____818
    then "?"
    else
      (let uu____825 =
         let uu____827 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____827 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____825)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v  ->
    let uu____839 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.major  in
    let uu____841 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____839 uu____841
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____867 = FStar_Options.hide_uvar_nums ()  in
    if uu____867
    then "?"
    else
      (let uu____874 =
         let uu____876 =
           let uu____878 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____878 FStar_Util.string_of_int  in
         let uu____882 =
           let uu____884 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.op_Hat ":" uu____884  in
         Prims.op_Hat uu____876 uu____882  in
       Prims.op_Hat "?" uu____874)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n  ->
    fun u  ->
      let uu____912 = FStar_Syntax_Subst.compress_univ u  in
      match uu____912 with
      | FStar_Syntax_Syntax.U_zero  -> (n, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 -> int_of_univ (n + Prims.int_one) u1
      | uu____925 -> (n, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____936 = FStar_Syntax_Subst.compress_univ u  in
    match uu____936 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____947 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____947
    | FStar_Syntax_Syntax.U_name x ->
        let uu____951 = FStar_Ident.text_of_id x  in
        Prims.op_Hat "U_name " uu____951
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____956 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____956
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____961 = int_of_univ Prims.int_one u1  in
        (match uu____961 with
         | (n,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n
         | (n,FStar_Pervasives_Native.Some u2) ->
             let uu____982 = univ_to_string u2  in
             let uu____984 = FStar_Util.string_of_int n  in
             FStar_Util.format2 "(%s + %s)" uu____982 uu____984)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____990 =
          let uu____992 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____992 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____990
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____1011 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____1011 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____1028 = FStar_List.map (fun x  -> FStar_Ident.text_of_id x) us
       in
    FStar_All.pipe_right uu____1028 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___4_1046  ->
    match uu___4_1046 with
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
        let uu____1062 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____1062
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1067 = lid_to_string l  in
        let uu____1069 = FStar_Ident.text_of_id x  in
        FStar_Util.format2 "(Projector %s %s)" uu____1067 uu____1069
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1082 =
          let uu____1084 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1084  in
        let uu____1085 =
          let uu____1087 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1087 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____1082 uu____1085
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1113 =
          let uu____1115 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1115  in
        let uu____1116 =
          let uu____1118 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1118 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1113 uu____1116
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1135 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____1135
    | FStar_Syntax_Syntax.ExceptionConstructor  -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect  -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect  -> "Effect"
    | FStar_Syntax_Syntax.Reifiable  -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        let uu____1143 = FStar_Ident.string_of_lid l  in
        FStar_Util.format1 "(reflect %s)" uu____1143
    | FStar_Syntax_Syntax.OnlyName  -> "OnlyName"
  
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1160 ->
        let uu____1163 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____1163 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1191 ->
        let uu____1194 = quals_to_string quals  in
        Prims.op_Hat uu____1194 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1376 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____1376
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1380 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____1380
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1384 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____1384
    | FStar_Syntax_Syntax.Tm_uinst uu____1387 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1395 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1397 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1399,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1400;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1414,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1415;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1429 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1449 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1465 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1473 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1491 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1515 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1543 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1558 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed uu____1572 -> "Tm_delayed-resolved"
    | FStar_Syntax_Syntax.Tm_meta (uu____1588,m) ->
        let uu____1594 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____1594
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1598 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1601 =
      let uu____1603 = FStar_Options.ugly ()  in Prims.op_Negation uu____1603
       in
    if uu____1601
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1617 = FStar_Options.print_implicits ()  in
         if uu____1617 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1625 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1642,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1668,thunk);
             FStar_Syntax_Syntax.ltyp = uu____1670;
             FStar_Syntax_Syntax.rng = uu____1671;_}
           ->
           let uu____1682 =
             let uu____1684 =
               let uu____1686 = FStar_Thunk.force thunk  in
               term_to_string uu____1686  in
             Prims.op_Hat uu____1684 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____1682
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1692 =
             let uu____1694 =
               let uu____1696 =
                 let uu____1697 =
                   let uu____1706 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1706  in
                 uu____1697 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1696  in
             Prims.op_Hat uu____1694 "]"  in
           Prims.op_Hat "[lazy:" uu____1692
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1775 =
                  match uu____1775 with
                  | (bv,t) ->
                      let uu____1783 = bv_to_string bv  in
                      let uu____1785 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1783 uu____1785
                   in
                let uu____1788 = term_to_string tm  in
                let uu____1790 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1788 uu____1790
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1799 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1799)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_pattern (uu____1803,ps)) ->
           let pats =
             let uu____1843 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1880 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1905  ->
                                 match uu____1905 with
                                 | (t1,uu____1914) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1880
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1843 (FStar_String.concat "\\/")  in
           let uu____1929 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1929
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1943 = tag_of_term t  in
           let uu____1945 = sli m  in
           let uu____1947 = term_to_string t'  in
           let uu____1949 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1943 uu____1945
             uu____1947 uu____1949
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1964 = tag_of_term t  in
           let uu____1966 = term_to_string t'  in
           let uu____1968 = sli m0  in
           let uu____1970 = sli m1  in
           let uu____1972 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1964
             uu____1966 uu____1968 uu____1970 uu____1972
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1987 = FStar_Range.string_of_range r  in
           let uu____1989 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1987
             uu____1989
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1998 = lid_to_string l  in
           let uu____2000 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____2002 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1998 uu____2000
             uu____2002
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____2006) ->
           let uu____2011 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2011
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2015 = db_to_string x3  in
           let uu____2017 =
             let uu____2019 =
               let uu____2021 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____2021 ")"  in
             Prims.op_Hat ":(" uu____2019  in
           Prims.op_Hat uu____2015 uu____2017
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2028)) ->
           let uu____2043 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2043
           then ctx_uvar_to_string u
           else
             (let uu____2049 =
                let uu____2051 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2051  in
              Prims.op_Hat "?" uu____2049)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2074 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2074
           then
             let uu____2078 = ctx_uvar_to_string u  in
             let uu____2080 =
               let uu____2082 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2082 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2078 uu____2080
           else
             (let uu____2101 =
                let uu____2103 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2103  in
              Prims.op_Hat "?" uu____2101)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2110 = FStar_Options.print_universes ()  in
           if uu____2110
           then
             let uu____2114 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2114
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2142 = binders_to_string " -> " bs  in
           let uu____2145 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2142 uu____2145
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2177 = binders_to_string " " bs  in
                let uu____2180 = term_to_string t2  in
                let uu____2182 =
                  FStar_Ident.string_of_lid
                    rc.FStar_Syntax_Syntax.residual_effect
                   in
                let uu____2184 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2193 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2193)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2177 uu____2180 uu____2182 uu____2184
            | uu____2197 ->
                let uu____2200 = binders_to_string " " bs  in
                let uu____2203 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2200 uu____2203)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2212 = bv_to_string xt  in
           let uu____2214 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2217 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2212 uu____2214 uu____2217
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2249 = term_to_string t  in
           let uu____2251 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2249 uu____2251
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2274 = lbs_to_string [] lbs  in
           let uu____2276 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2274 uu____2276
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2341 =
                   let uu____2343 =
                     FStar_Util.map_opt eff_name FStar_Ident.string_of_lid
                      in
                   FStar_All.pipe_right uu____2343
                     (FStar_Util.dflt "default")
                    in
                 let uu____2354 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2341 uu____2354
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2375 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2375
              in
           let uu____2378 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2378 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head,branches) ->
           let uu____2419 = term_to_string head  in
           let uu____2421 =
             let uu____2423 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string)
                in
             FStar_Util.concat_l "\n\t|" uu____2423  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2419 uu____2421
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2441 = FStar_Options.print_universes ()  in
           if uu____2441
           then
             let uu____2445 = term_to_string t  in
             let uu____2447 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2445 uu____2447
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____2453  ->
    match uu____2453 with
    | (p,wopt,e) ->
        let uu____2475 = FStar_All.pipe_right p pat_to_string  in
        let uu____2478 =
          match wopt with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____2489 = FStar_All.pipe_right w term_to_string  in
              FStar_Util.format1 "when %s" uu____2489
           in
        let uu____2493 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format3 "%s %s -> %s" uu____2475 uu____2478 uu____2493

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2498 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2501 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2503 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2498 uu____2501
      uu____2503

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2506  ->
    match uu___5_2506 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2512 = FStar_Util.string_of_int i  in
        let uu____2514 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2512 uu____2514
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2521 = bv_to_string x  in
        let uu____2523 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2521 uu____2523
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2532 = bv_to_string x  in
        let uu____2534 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2532 uu____2534
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2541 = FStar_Util.string_of_int i  in
        let uu____2543 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2541 uu____2543
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2550 = FStar_Ident.text_of_id u  in
        let uu____2552 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" uu____2550 uu____2552

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2556 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2556 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2572 =
      let uu____2574 = FStar_Options.ugly ()  in Prims.op_Negation uu____2574
       in
    if uu____2572
    then
      let e =
        let uu____2579 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2579  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2608 = fv_to_string l  in
           let uu____2610 =
             let uu____2612 =
               FStar_List.map
                 (fun uu____2626  ->
                    match uu____2626 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2612 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2608 uu____2610
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2651) ->
           let uu____2656 = FStar_Options.print_bound_var_types ()  in
           if uu____2656
           then
             let uu____2660 = bv_to_string x1  in
             let uu____2662 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2660 uu____2662
           else
             (let uu____2667 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2667)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2671 = FStar_Options.print_bound_var_types ()  in
           if uu____2671
           then
             let uu____2675 = bv_to_string x1  in
             let uu____2677 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2675 uu____2677
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2684 = FStar_Options.print_bound_var_types ()  in
           if uu____2684
           then
             let uu____2688 = bv_to_string x1  in
             let uu____2690 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2688 uu____2690
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2699 = quals_to_string' quals  in
      let uu____2701 =
        let uu____2703 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2723 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2725 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2727 =
                    let uu____2729 = FStar_Options.print_universes ()  in
                    if uu____2729
                    then
                      let uu____2733 =
                        let uu____2735 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____2735 ">"  in
                      Prims.op_Hat "<" uu____2733
                    else ""  in
                  let uu____2742 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2744 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2723
                    uu____2725 uu____2727 uu____2742 uu____2744))
           in
        FStar_Util.concat_l "\n and " uu____2703  in
      FStar_Util.format3 "%slet %s %s" uu____2699
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2701

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2759  ->
    match uu___6_2759 with
    | [] -> ""
    | tms ->
        let uu____2767 =
          let uu____2769 =
            FStar_List.map
              (fun t  ->
                 let uu____2777 = term_to_string t  in paren uu____2777) tms
             in
          FStar_All.pipe_right uu____2769 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2767

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___7_2786  ->
      match uu___7_2786 with
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
          let uu____2804 =
            let uu____2806 = term_to_string t  in
            Prims.op_Hat uu____2806 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____2804
      | FStar_Pervasives_Native.None  -> s

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
      let uu____2824 =
        let uu____2826 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2826  in
      if uu____2824
      then
        let uu____2830 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2830 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
        (let uu____2841 = b  in
         match uu____2841 with
         | (a,imp) ->
             let uu____2855 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2855
             then
               let uu____2859 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat "_:" uu____2859
             else
               (let uu____2864 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2867 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2867)
                   in
                if uu____2864
                then
                  let uu____2871 = nm_to_string a  in
                  imp_to_string uu____2871 imp
                else
                  (let uu____2875 =
                     let uu____2877 = nm_to_string a  in
                     let uu____2879 =
                       let uu____2881 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____2881  in
                     Prims.op_Hat uu____2877 uu____2879  in
                   imp_to_string uu____2875 imp)))

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
        let uu____2900 = FStar_Options.print_implicits ()  in
        if uu____2900 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2911 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2911 (FStar_String.concat sep)
      else
        (let uu____2939 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2939 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_2953  ->
    match uu___8_2953 with
    | (a,imp) ->
        let uu____2967 = term_to_string a  in imp_to_string uu____2967 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2979 = FStar_Options.print_implicits ()  in
      if uu____2979 then args else filter_imp args  in
    let uu____2994 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2994 (FStar_String.concat " ")

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____3022 =
      let uu____3024 = FStar_Options.ugly ()  in Prims.op_Negation uu____3024
       in
    if uu____3022
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____3045 =
             let uu____3046 = FStar_Syntax_Subst.compress t  in
             uu____3046.FStar_Syntax_Syntax.n  in
           (match uu____3045 with
            | FStar_Syntax_Syntax.Tm_type uu____3050 when
                let uu____3051 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3051 -> term_to_string t
            | uu____3053 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3056 = univ_to_string u  in
                     let uu____3058 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3056 uu____3058
                 | uu____3061 ->
                     let uu____3064 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3064))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3077 =
             let uu____3078 = FStar_Syntax_Subst.compress t  in
             uu____3078.FStar_Syntax_Syntax.n  in
           (match uu____3077 with
            | FStar_Syntax_Syntax.Tm_type uu____3082 when
                let uu____3083 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3083 -> term_to_string t
            | uu____3085 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3088 = univ_to_string u  in
                     let uu____3090 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3088 uu____3090
                 | uu____3093 ->
                     let uu____3096 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3096))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3102 = FStar_Options.print_effect_args ()  in
             if uu____3102
             then
               let uu____3106 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3108 =
                 let uu____3110 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3110 (FStar_String.concat ", ")
                  in
               let uu____3125 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3127 =
                 let uu____3129 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3129 (FStar_String.concat ", ")
                  in
               let uu____3156 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3106
                 uu____3108 uu____3125 uu____3127 uu____3156
             else
               (let uu____3161 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3167  ->
                           match uu___9_3167 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3170 -> false)))
                    &&
                    (let uu____3173 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3173)
                   in
                if uu____3161
                then
                  let uu____3177 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3177
                else
                  (let uu____3182 =
                     ((let uu____3186 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3186) &&
                        (let uu____3189 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3189))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____3182
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3195 =
                        (let uu____3199 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3199) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3205  ->
                                   match uu___10_3205 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3208 -> false)))
                         in
                      if uu____3195
                      then
                        let uu____3212 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3212
                      else
                        (let uu____3217 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3219 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3217 uu____3219))))
              in
           let dec =
             let uu____3224 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3237  ->
                       match uu___11_3237 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3244 =
                             let uu____3246 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3246
                              in
                           [uu____3244]
                       | uu____3251 -> []))
                in
             FStar_All.pipe_right uu____3224 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____3270 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_3280  ->
    match uu___12_3280 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____3282,ps) ->
        let pats =
          let uu____3318 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3355 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3380  ->
                              match uu____3380 with
                              | (t,uu____3389) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3355
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3318 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3406 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3406
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3411) ->
        let uu____3416 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3416
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____3427 = sli m  in
        let uu____3429 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3427 uu____3429
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3439 = sli m  in
        let uu____3441 = sli m'  in
        let uu____3443 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3439
          uu____3441 uu____3443

let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq  -> aqual_to_string' "" aq 
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____3466 = FStar_Options.ugly ()  in
      if uu____3466
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)
  
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____3488 = FStar_Options.ugly ()  in
      if uu____3488
      then term_to_string x
      else
        (let e = FStar_Syntax_Resugar.resugar_term' env x  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)
  
let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env  ->
    fun b  ->
      let uu____3509 = b  in
      match uu____3509 with
      | (a,imp) ->
          let n =
            let uu____3517 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3517
            then FStar_Util.JsonNull
            else
              (let uu____3522 =
                 let uu____3524 = nm_to_string a  in
                 imp_to_string uu____3524 imp  in
               FStar_Util.JsonStr uu____3522)
             in
          let t =
            let uu____3527 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3527  in
          FStar_Util.JsonAssoc [("name", n); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____3559 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3559
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3577 = FStar_Options.print_universes ()  in
    if uu____3577 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3593 =
      let uu____3595 = FStar_Options.ugly ()  in Prims.op_Negation uu____3595
       in
    if uu____3593
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
      (let uu____3605 = s  in
       match uu____3605 with
       | (us,t) ->
           let uu____3617 =
             let uu____3619 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3619  in
           let uu____3623 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3617 uu____3623)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3633 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3635 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3638 =
      let uu____3640 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3640  in
    let uu____3644 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3646 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3633 uu____3635 uu____3638
      uu____3644 uu____3646
  
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs  ->
    let tscheme_opt_to_string uu___13_3664 =
      match uu___13_3664 with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None  -> "None"  in
    let uu____3670 =
      let uu____3674 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____3676 =
        let uu____3680 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp
           in
        let uu____3682 =
          let uu____3686 =
            tscheme_to_string combs.FStar_Syntax_Syntax.stronger  in
          let uu____3688 =
            let uu____3692 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else  in
            let uu____3694 =
              let uu____3698 =
                tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp  in
              let uu____3700 =
                let uu____3704 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp  in
                let uu____3706 =
                  let uu____3710 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial  in
                  let uu____3712 =
                    let uu____3716 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr
                       in
                    let uu____3718 =
                      let uu____3722 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr
                         in
                      let uu____3724 =
                        let uu____3728 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr
                           in
                        [uu____3728]  in
                      uu____3722 :: uu____3724  in
                    uu____3716 :: uu____3718  in
                  uu____3710 :: uu____3712  in
                uu____3704 :: uu____3706  in
              uu____3698 :: uu____3700  in
            uu____3692 :: uu____3694  in
          uu____3686 :: uu____3688  in
        uu____3680 :: uu____3682  in
      uu____3674 :: uu____3676  in
    FStar_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu____3670
  
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs  ->
    let to_str uu____3759 =
      match uu____3759 with
      | (ts_t,ts_ty) ->
          let uu____3767 = tscheme_to_string ts_t  in
          let uu____3769 = tscheme_to_string ts_ty  in
          FStar_Util.format2 "(%s) : (%s)" uu____3767 uu____3769
       in
    let uu____3772 =
      let uu____3776 =
        FStar_Ident.string_of_lid combs.FStar_Syntax_Syntax.l_base_effect  in
      let uu____3778 =
        let uu____3782 = to_str combs.FStar_Syntax_Syntax.l_repr  in
        let uu____3784 =
          let uu____3788 = to_str combs.FStar_Syntax_Syntax.l_return  in
          let uu____3790 =
            let uu____3794 = to_str combs.FStar_Syntax_Syntax.l_bind  in
            let uu____3796 =
              let uu____3800 = to_str combs.FStar_Syntax_Syntax.l_subcomp  in
              let uu____3802 =
                let uu____3806 =
                  to_str combs.FStar_Syntax_Syntax.l_if_then_else  in
                [uu____3806]  in
              uu____3800 :: uu____3802  in
            uu____3794 :: uu____3796  in
          uu____3788 :: uu____3790  in
        uu____3782 :: uu____3784  in
      uu____3776 :: uu____3778  in
    FStar_Util.format
      "{\nl_base_effect = %s\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  }\n"
      uu____3772
  
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___14_3822  ->
    match uu___14_3822 with
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
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____3855 =
            let uu____3857 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3857  in
          if uu____3855
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
               let uu____3878 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3878 (FStar_String.concat ",\n\t")
                in
             let eff_name =
               let uu____3895 = FStar_Syntax_Util.is_layered ed  in
               if uu____3895 then "layered_effect" else "new_effect"  in
             let uu____3903 =
               let uu____3907 =
                 let uu____3911 =
                   let uu____3915 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname  in
                   let uu____3917 =
                     let uu____3921 =
                       let uu____3923 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs
                          in
                       FStar_All.pipe_left enclose_universes uu____3923  in
                     let uu____3927 =
                       let uu____3931 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders
                          in
                       let uu____3934 =
                         let uu____3938 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature
                            in
                         let uu____3940 =
                           let uu____3944 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____3946 =
                             let uu____3950 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions
                                in
                             [uu____3950]  in
                           uu____3944 :: uu____3946  in
                         uu____3938 :: uu____3940  in
                       uu____3931 :: uu____3934  in
                     uu____3921 :: uu____3927  in
                   uu____3915 :: uu____3917  in
                 (if for_free then "_for_free " else "") :: uu____3911  in
               eff_name :: uu____3907  in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu____3903)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se  ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
        let uu____4002 = FStar_All.pipe_right ts_opt FStar_Util.must  in
        FStar_All.pipe_right uu____4002 tscheme_to_string
      else "<None>"  in
    let uu____4009 = lid_to_string se.FStar_Syntax_Syntax.source  in
    let uu____4011 = lid_to_string se.FStar_Syntax_Syntax.target  in
    let uu____4013 = tsopt_to_string se.FStar_Syntax_Syntax.lift  in
    let uu____4015 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp  in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____4009 uu____4011 uu____4013 uu____4015
  
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
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
          -> "#restart-solver"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
          "#pop-options"
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univs,tps,k,uu____4050,uu____4051) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4067 = FStar_Options.print_universes ()  in
          if uu____4067
          then
            let uu____4071 = FStar_Ident.string_of_lid lid  in
            let uu____4073 = univ_names_to_string univs  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str uu____4071
              uu____4073 binders_str term_str
          else
            (let uu____4078 = FStar_Ident.string_of_lid lid  in
             FStar_Util.format4 "%stype %s %s : %s" quals_str uu____4078
               binders_str term_str)
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs,t,uu____4084,uu____4085,uu____4086) ->
          let uu____4093 = FStar_Options.print_universes ()  in
          if uu____4093
          then
            let uu____4097 = univ_names_to_string univs  in
            let uu____4099 = FStar_Ident.string_of_lid lid  in
            let uu____4101 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4097 uu____4099
              uu____4101
          else
            (let uu____4106 = FStar_Ident.string_of_lid lid  in
             let uu____4108 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" uu____4106 uu____4108)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs,t) ->
          let uu____4114 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4116 = FStar_Ident.string_of_lid lid  in
          let uu____4118 =
            let uu____4120 = FStar_Options.print_universes ()  in
            if uu____4120
            then
              let uu____4124 = univ_names_to_string univs  in
              FStar_Util.format1 "<%s>" uu____4124
            else ""  in
          let uu____4130 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4114 uu____4116
            uu____4118 uu____4130
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4136 = FStar_Options.print_universes ()  in
          if uu____4136
          then
            let uu____4140 = FStar_Ident.string_of_lid lid  in
            let uu____4142 = univ_names_to_string us  in
            let uu____4144 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" uu____4140 uu____4142
              uu____4144
          else
            (let uu____4149 = FStar_Ident.string_of_lid lid  in
             let uu____4151 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" uu____4149 uu____4151)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4155) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4161 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____4161
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4165) ->
          let uu____4174 =
            let uu____4176 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4176 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____4174
      | FStar_Syntax_Syntax.Sig_fail (errs,lax,ses) ->
          let uu____4202 = FStar_Util.string_of_bool lax  in
          let uu____4204 =
            FStar_Common.string_of_list FStar_Util.string_of_int errs  in
          let uu____4207 =
            let uu____4209 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4209 (FStar_String.concat "\n")  in
          FStar_Util.format3 "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n"
            uu____4202 uu____4204 uu____4207
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4221 = FStar_Syntax_Util.is_dm4f ed  in
          eff_decl_to_string' uu____4221 x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs,tps,c,flags) ->
          let uu____4233 = FStar_Options.print_universes ()  in
          if uu____4233
          then
            let uu____4237 =
              let uu____4242 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs uu____4242  in
            (match uu____4237 with
             | (univs1,t) ->
                 let uu____4256 =
                   let uu____4261 =
                     let uu____4262 = FStar_Syntax_Subst.compress t  in
                     uu____4262.FStar_Syntax_Syntax.n  in
                   match uu____4261 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4291 -> failwith "impossible"  in
                 (match uu____4256 with
                  | (tps1,c1) ->
                      let uu____4300 = sli l  in
                      let uu____4302 = univ_names_to_string univs1  in
                      let uu____4304 = binders_to_string " " tps1  in
                      let uu____4307 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4300
                        uu____4302 uu____4304 uu____4307))
          else
            (let uu____4312 = sli l  in
             let uu____4314 = binders_to_string " " tps  in
             let uu____4317 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4312 uu____4314
               uu____4317)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4326 =
            let uu____4328 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4328  in
          let uu____4338 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4326 uu____4338
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,t,ty) ->
          let uu____4346 = FStar_Ident.string_of_lid m  in
          let uu____4348 = FStar_Ident.string_of_lid n  in
          let uu____4350 = FStar_Ident.string_of_lid p  in
          let uu____4352 = tscheme_to_string t  in
          let uu____4354 = tscheme_to_string ty  in
          FStar_Util.format5 "polymonadic_bind (%s, %s) |> %s = (%s, %s)"
            uu____4346 uu____4348 uu____4350 uu____4352 uu____4354
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp (m,n,t,ty) ->
          let uu____4361 = FStar_Ident.string_of_lid m  in
          let uu____4363 = FStar_Ident.string_of_lid n  in
          let uu____4365 = tscheme_to_string t  in
          let uu____4367 = tscheme_to_string ty  in
          FStar_Util.format4 "polymonadic_subcomp %s <: %s = (%s, %s)"
            uu____4361 uu____4363 uu____4365 uu____4367
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4373 ->
        let uu____4376 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____4376 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____4393 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4393 msg
  
let (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4404,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4406;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4408;
                       FStar_Syntax_Syntax.lbdef = uu____4409;
                       FStar_Syntax_Syntax.lbattrs = uu____4410;
                       FStar_Syntax_Syntax.lbpos = uu____4411;_}::[]),uu____4412)
        ->
        let uu____4435 = lbname_to_string lb  in
        let uu____4437 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4435 uu____4437
    | uu____4440 ->
        let uu____4441 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> FStar_Ident.string_of_lid l))
           in
        FStar_All.pipe_right uu____4441 (FStar_String.concat ", ")
  
let (tag_of_sigelt : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4467 -> "Sig_inductive_typ"
    | FStar_Syntax_Syntax.Sig_bundle uu____4485 -> "Sig_bundle"
    | FStar_Syntax_Syntax.Sig_datacon uu____4495 -> "Sig_datacon"
    | FStar_Syntax_Syntax.Sig_declare_typ uu____4512 -> "Sig_declare_typ"
    | FStar_Syntax_Syntax.Sig_let uu____4520 -> "Sig_let"
    | FStar_Syntax_Syntax.Sig_main uu____4528 -> "Sig_main"
    | FStar_Syntax_Syntax.Sig_assume uu____4530 -> "Sig_assume"
    | FStar_Syntax_Syntax.Sig_new_effect uu____4538 -> "Sig_new_effect"
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4540 -> "Sig_sub_effect"
    | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4542 -> "Sig_effect_abbrev"
    | FStar_Syntax_Syntax.Sig_pragma uu____4556 -> "Sig_pragma"
    | FStar_Syntax_Syntax.Sig_splice uu____4558 -> "Sig_splice"
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____4566 ->
        "Sig_polymonadic_bind"
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____4578 ->
        "Sig_polymonadic_subcomp"
    | FStar_Syntax_Syntax.Sig_fail uu____4588 -> "Sig_fail"
  
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4609 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4611 =
      let uu____4613 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4613 (FStar_String.concat "\n")  in
    let uu____4623 =
      let uu____4625 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4625 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4609
      uu____4611 uu____4623
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
           (let uu____4675 = f x  in
            FStar_Util.string_builder_append strb uu____4675);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4684 = f x1  in
                 FStar_Util.string_builder_append strb uu____4684)) xs;
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
           (let uu____4731 = f x  in
            FStar_Util.string_builder_append strb uu____4731);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4740 = f x1  in
                 FStar_Util.string_builder_append strb uu____4740)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____4762 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4762
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___15_4775  ->
    match uu___15_4775 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4791 =
          let uu____4793 =
            let uu____4795 =
              let uu____4797 =
                let uu____4799 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4799 (FStar_String.concat " ")  in
              Prims.op_Hat uu____4797 ")"  in
            Prims.op_Hat " " uu____4795  in
          Prims.op_Hat h uu____4793  in
        Prims.op_Hat "(" uu____4791
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4814 =
          let uu____4816 = emb_typ_to_string a  in
          let uu____4818 =
            let uu____4820 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____4820  in
          Prims.op_Hat uu____4816 uu____4818  in
        Prims.op_Hat "(" uu____4814
  