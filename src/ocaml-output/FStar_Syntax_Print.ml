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
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____59 =
      let uu____61 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____61  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____59
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____71 = FStar_Options.print_real_names ()  in
    if uu____71
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____84 =
      let uu____86 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____86  in
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
  fun ps  ->
    fun f  ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____308 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____321 -> failwith "get_lid"
  
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
  'Auu____424 'Auu____425 .
    ('Auu____424,'Auu____425) FStar_Util.either -> Prims.bool
  =
  fun uu___1_435  ->
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
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___2_504  ->
            match uu___2_504 with
            | (uu____512,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____519,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____520)) -> false
            | (uu____525,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____526)) -> false
            | uu____532 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____550 =
      let uu____551 = FStar_Syntax_Subst.compress e  in
      uu____551.FStar_Syntax_Syntax.n  in
    match uu____550 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____612 =
          (is_lex_cons f) && ((FStar_List.length exps) = (Prims.of_int (2)))
           in
        if uu____612
        then
          let uu____621 =
            let uu____626 = FStar_List.nth exps Prims.int_one  in
            reconstruct_lex uu____626  in
          (match uu____621 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____637 =
                 let uu____640 = FStar_List.nth exps Prims.int_zero  in
                 uu____640 :: xs  in
               FStar_Pervasives_Native.Some uu____637
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____652 ->
        let uu____653 = is_lex_top e  in
        if uu____653
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____701 = f hd1  in if uu____701 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____733 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____733
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____764 = get_lid e  in find_lid uu____764 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____776 = get_lid e  in find_lid uu____776 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____788 = get_lid t  in find_lid uu____788 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___3_802  ->
    match uu___3_802 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____813 = FStar_Options.hide_uvar_nums ()  in
    if uu____813
    then "?"
    else
      (let uu____820 =
         let uu____822 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____822 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____820)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____834 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____836 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____834 uu____836
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____862 = FStar_Options.hide_uvar_nums ()  in
    if uu____862
    then "?"
    else
      (let uu____869 =
         let uu____871 =
           let uu____873 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____873 FStar_Util.string_of_int  in
         let uu____877 =
           let uu____879 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.op_Hat ":" uu____879  in
         Prims.op_Hat uu____871 uu____877  in
       Prims.op_Hat "?" uu____869)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____907 = FStar_Syntax_Subst.compress_univ u  in
      match uu____907 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 -> int_of_univ (n1 + Prims.int_one) u1
      | uu____920 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____931 = FStar_Syntax_Subst.compress_univ u  in
    match uu____931 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____942 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____942
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____949 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____949
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____954 = int_of_univ Prims.int_one u1  in
        (match uu____954 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____975 = univ_to_string u2  in
             let uu____977 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____975 uu____977)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____983 =
          let uu____985 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____985 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____983
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____1004 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____1004 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____1021 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____1021 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___4_1039  ->
    match uu___4_1039 with
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
        let uu____1055 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____1055
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1060 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____1060
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1073 =
          let uu____1075 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1075  in
        let uu____1076 =
          let uu____1078 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1078 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____1073 uu____1076
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1104 =
          let uu____1106 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1106  in
        let uu____1107 =
          let uu____1109 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1109 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1104 uu____1107
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1126 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____1126
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
    | uu____1149 ->
        let uu____1152 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____1152 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1180 ->
        let uu____1183 = quals_to_string quals  in
        Prims.op_Hat uu____1183 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1379 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____1379
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1383 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____1383
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1387 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____1387
    | FStar_Syntax_Syntax.Tm_uinst uu____1390 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1398 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1400 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1402,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1403;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1417,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
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
    | FStar_Syntax_Syntax.Tm_delayed (uu____1575,m) ->
        let uu____1613 = FStar_ST.op_Bang m  in
        (match uu____1613 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1649 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1655,m) ->
        let uu____1661 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____1661
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1665 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1668 =
      let uu____1670 = FStar_Options.ugly ()  in Prims.op_Negation uu____1670
       in
    if uu____1668
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1684 = FStar_Options.print_implicits ()  in
         if uu____1684 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1692 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1717,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1743,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____1745;
             FStar_Syntax_Syntax.rng = uu____1746;_}
           ->
           let uu____1757 =
             let uu____1759 =
               let uu____1761 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____1761  in
             Prims.op_Hat uu____1759 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____1757
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1767 =
             let uu____1769 =
               let uu____1771 =
                 let uu____1772 =
                   let uu____1781 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1781  in
                 uu____1772 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1771  in
             Prims.op_Hat uu____1769 "]"  in
           Prims.op_Hat "[lazy:" uu____1767
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1850 =
                  match uu____1850 with
                  | (bv,t) ->
                      let uu____1858 = bv_to_string bv  in
                      let uu____1860 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1858 uu____1860
                   in
                let uu____1863 = term_to_string tm  in
                let uu____1865 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1863 uu____1865
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1874 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1874)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_pattern (uu____1878,ps)) ->
           let pats =
             let uu____1918 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1955 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1980  ->
                                 match uu____1980 with
                                 | (t1,uu____1989) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1955
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1918 (FStar_String.concat "\\/")  in
           let uu____2004 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____2004
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____2018 = tag_of_term t  in
           let uu____2020 = sli m  in
           let uu____2022 = term_to_string t'  in
           let uu____2024 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____2018 uu____2020
             uu____2022 uu____2024
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____2039 = tag_of_term t  in
           let uu____2041 = term_to_string t'  in
           let uu____2043 = sli m0  in
           let uu____2045 = sli m1  in
           let uu____2047 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2039
             uu____2041 uu____2043 uu____2045 uu____2047
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____2062 = FStar_Range.string_of_range r  in
           let uu____2064 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2062
             uu____2064
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2073 = lid_to_string l  in
           let uu____2075 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____2077 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2073 uu____2075
             uu____2077
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____2081) ->
           let uu____2086 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2086
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2090 = db_to_string x3  in
           let uu____2092 =
             let uu____2094 =
               let uu____2096 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____2096 ")"  in
             Prims.op_Hat ":(" uu____2094  in
           Prims.op_Hat uu____2090 uu____2092
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2103)) ->
           let uu____2118 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2118
           then ctx_uvar_to_string u
           else
             (let uu____2124 =
                let uu____2126 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2126  in
              Prims.op_Hat "?" uu____2124)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2149 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2149
           then
             let uu____2153 = ctx_uvar_to_string u  in
             let uu____2155 =
               let uu____2157 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2157 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2153 uu____2155
           else
             (let uu____2176 =
                let uu____2178 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2178  in
              Prims.op_Hat "?" uu____2176)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2185 = FStar_Options.print_universes ()  in
           if uu____2185
           then
             let uu____2189 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2189
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2217 = binders_to_string " -> " bs  in
           let uu____2220 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2217 uu____2220
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2252 = binders_to_string " " bs  in
                let uu____2255 = term_to_string t2  in
                let uu____2257 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2266 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2266)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2252 uu____2255
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____2257
            | uu____2270 ->
                let uu____2273 = binders_to_string " " bs  in
                let uu____2276 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2273 uu____2276)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2285 = bv_to_string xt  in
           let uu____2287 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2290 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2285 uu____2287 uu____2290
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2322 = term_to_string t  in
           let uu____2324 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2322 uu____2324
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2347 = lbs_to_string [] lbs  in
           let uu____2349 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2347 uu____2349
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2414 =
                   let uu____2416 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____2416
                     (FStar_Util.dflt "default")
                    in
                 let uu____2427 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2414 uu____2427
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2448 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2448
              in
           let uu____2451 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2451 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____2492 = term_to_string head1  in
           let uu____2494 =
             let uu____2496 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string)
                in
             FStar_Util.concat_l "\n\t|" uu____2496  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2492 uu____2494
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2514 = FStar_Options.print_universes ()  in
           if uu____2514
           then
             let uu____2518 = term_to_string t  in
             let uu____2520 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2518 uu____2520
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____2526  ->
    match uu____2526 with
    | (p,wopt,e) ->
        let uu____2548 = FStar_All.pipe_right p pat_to_string  in
        let uu____2551 =
          match wopt with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____2562 = FStar_All.pipe_right w term_to_string  in
              FStar_Util.format1 "when %s" uu____2562
           in
        let uu____2566 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format3 "%s %s -> %s" uu____2548 uu____2551 uu____2566

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2571 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2574 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2576 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2571 uu____2574
      uu____2576

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2579  ->
    match uu___5_2579 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2585 = FStar_Util.string_of_int i  in
        let uu____2587 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2585 uu____2587
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2594 = bv_to_string x  in
        let uu____2596 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2594 uu____2596
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2605 = bv_to_string x  in
        let uu____2607 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2605 uu____2607
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2614 = FStar_Util.string_of_int i  in
        let uu____2616 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2614 uu____2616
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2623 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2623

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2627 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2627 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2643 =
      let uu____2645 = FStar_Options.ugly ()  in Prims.op_Negation uu____2645
       in
    if uu____2643
    then
      let e =
        let uu____2650 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2650  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2679 = fv_to_string l  in
           let uu____2681 =
             let uu____2683 =
               FStar_List.map
                 (fun uu____2697  ->
                    match uu____2697 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2683 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2679 uu____2681
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2722) ->
           let uu____2727 = FStar_Options.print_bound_var_types ()  in
           if uu____2727
           then
             let uu____2731 = bv_to_string x1  in
             let uu____2733 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2731 uu____2733
           else
             (let uu____2738 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2738)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2742 = FStar_Options.print_bound_var_types ()  in
           if uu____2742
           then
             let uu____2746 = bv_to_string x1  in
             let uu____2748 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2746 uu____2748
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2755 = FStar_Options.print_bound_var_types ()  in
           if uu____2755
           then
             let uu____2759 = bv_to_string x1  in
             let uu____2761 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2759 uu____2761
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2770 = quals_to_string' quals  in
      let uu____2772 =
        let uu____2774 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2794 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2796 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2798 =
                    let uu____2800 = FStar_Options.print_universes ()  in
                    if uu____2800
                    then
                      let uu____2804 =
                        let uu____2806 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____2806 ">"  in
                      Prims.op_Hat "<" uu____2804
                    else ""  in
                  let uu____2813 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2815 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2794
                    uu____2796 uu____2798 uu____2813 uu____2815))
           in
        FStar_Util.concat_l "\n and " uu____2774  in
      FStar_Util.format3 "%slet %s %s" uu____2770
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2772

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2830  ->
    match uu___6_2830 with
    | [] -> ""
    | tms ->
        let uu____2838 =
          let uu____2840 =
            FStar_List.map
              (fun t  ->
                 let uu____2848 = term_to_string t  in paren uu____2848) tms
             in
          FStar_All.pipe_right uu____2840 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2838

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___7_2857  ->
      match uu___7_2857 with
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
          let uu____2875 =
            let uu____2877 = term_to_string t  in
            Prims.op_Hat uu____2877 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____2875
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
      let uu____2897 =
        let uu____2899 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2899  in
      if uu____2897
      then
        let uu____2903 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2903 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
        (let uu____2914 = b  in
         match uu____2914 with
         | (a,imp) ->
             let uu____2928 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2928
             then
               let uu____2932 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat "_:" uu____2932
             else
               (let uu____2937 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2940 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2940)
                   in
                if uu____2937
                then
                  let uu____2944 = nm_to_string a  in
                  imp_to_string uu____2944 imp
                else
                  (let uu____2948 =
                     let uu____2950 = nm_to_string a  in
                     let uu____2952 =
                       let uu____2954 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____2954  in
                     Prims.op_Hat uu____2950 uu____2952  in
                   imp_to_string uu____2948 imp)))

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
        let uu____2973 = FStar_Options.print_implicits ()  in
        if uu____2973 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2984 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2984 (FStar_String.concat sep)
      else
        (let uu____3012 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____3012 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_3026  ->
    match uu___8_3026 with
    | (a,imp) ->
        let uu____3040 = term_to_string a  in imp_to_string uu____3040 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____3052 = FStar_Options.print_implicits ()  in
      if uu____3052 then args else filter_imp args  in
    let uu____3067 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____3067 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____3096 = FStar_Options.ugly ()  in
      if uu____3096
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____3107 =
      let uu____3109 = FStar_Options.ugly ()  in Prims.op_Negation uu____3109
       in
    if uu____3107
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____3130 =
             let uu____3131 = FStar_Syntax_Subst.compress t  in
             uu____3131.FStar_Syntax_Syntax.n  in
           (match uu____3130 with
            | FStar_Syntax_Syntax.Tm_type uu____3135 when
                let uu____3136 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3136 -> term_to_string t
            | uu____3138 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3141 = univ_to_string u  in
                     let uu____3143 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3141 uu____3143
                 | uu____3146 ->
                     let uu____3149 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3149))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3162 =
             let uu____3163 = FStar_Syntax_Subst.compress t  in
             uu____3163.FStar_Syntax_Syntax.n  in
           (match uu____3162 with
            | FStar_Syntax_Syntax.Tm_type uu____3167 when
                let uu____3168 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3168 -> term_to_string t
            | uu____3170 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3173 = univ_to_string u  in
                     let uu____3175 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3173 uu____3175
                 | uu____3178 ->
                     let uu____3181 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3181))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3187 = FStar_Options.print_effect_args ()  in
             if uu____3187
             then
               let uu____3191 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3193 =
                 let uu____3195 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3195 (FStar_String.concat ", ")
                  in
               let uu____3210 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3212 =
                 let uu____3214 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3214 (FStar_String.concat ", ")
                  in
               let uu____3241 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3191
                 uu____3193 uu____3210 uu____3212 uu____3241
             else
               (let uu____3246 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3252  ->
                           match uu___9_3252 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3255 -> false)))
                    &&
                    (let uu____3258 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3258)
                   in
                if uu____3246
                then
                  let uu____3262 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3262
                else
                  (let uu____3267 =
                     ((let uu____3271 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3271) &&
                        (let uu____3274 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3274))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____3267
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3280 =
                        (let uu____3284 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3284) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3290  ->
                                   match uu___10_3290 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3293 -> false)))
                         in
                      if uu____3280
                      then
                        let uu____3297 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3297
                      else
                        (let uu____3302 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3304 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3302 uu____3304))))
              in
           let dec =
             let uu____3309 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3322  ->
                       match uu___11_3322 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3329 =
                             let uu____3331 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3331
                              in
                           [uu____3329]
                       | uu____3336 -> []))
                in
             FStar_All.pipe_right uu____3309 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____3355 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_3365  ->
    match uu___12_3365 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____3367,ps) ->
        let pats =
          let uu____3403 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3440 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3465  ->
                              match uu____3465 with
                              | (t,uu____3474) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3440
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3403 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3491 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3491
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3496) ->
        let uu____3501 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3501
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____3512 = sli m  in
        let uu____3514 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3512 uu____3514
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3524 = sli m  in
        let uu____3526 = sli m'  in
        let uu____3528 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3524
          uu____3526 uu____3528

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____3543 = FStar_Options.ugly ()  in
      if uu____3543
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
      let uu____3564 = b  in
      match uu____3564 with
      | (a,imp) ->
          let n1 =
            let uu____3572 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3572
            then FStar_Util.JsonNull
            else
              (let uu____3577 =
                 let uu____3579 = nm_to_string a  in
                 imp_to_string uu____3579 imp  in
               FStar_Util.JsonStr uu____3577)
             in
          let t =
            let uu____3582 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3582  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____3614 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3614
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3632 = FStar_Options.print_universes ()  in
    if uu____3632 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3648 =
      let uu____3650 = FStar_Options.ugly ()  in Prims.op_Negation uu____3650
       in
    if uu____3648
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
      (let uu____3660 = s  in
       match uu____3660 with
       | (us,t) ->
           let uu____3672 =
             let uu____3674 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3674  in
           let uu____3678 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3672 uu____3678)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3688 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3690 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3693 =
      let uu____3695 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3695  in
    let uu____3699 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3701 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3688 uu____3690 uu____3693
      uu____3699 uu____3701
  
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs  ->
    let tscheme_opt_to_string uu___13_3719 =
      match uu___13_3719 with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None  -> "None"  in
    let uu____3725 =
      let uu____3729 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____3731 =
        let uu____3735 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp
           in
        let uu____3737 =
          let uu____3741 =
            tscheme_to_string combs.FStar_Syntax_Syntax.stronger  in
          let uu____3743 =
            let uu____3747 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else  in
            let uu____3749 =
              let uu____3753 =
                tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp  in
              let uu____3755 =
                let uu____3759 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp  in
                let uu____3761 =
                  let uu____3765 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial  in
                  let uu____3767 =
                    let uu____3771 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr
                       in
                    let uu____3773 =
                      let uu____3777 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr
                         in
                      let uu____3779 =
                        let uu____3783 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr
                           in
                        [uu____3783]  in
                      uu____3777 :: uu____3779  in
                    uu____3771 :: uu____3773  in
                  uu____3765 :: uu____3767  in
                uu____3759 :: uu____3761  in
              uu____3753 :: uu____3755  in
            uu____3747 :: uu____3749  in
          uu____3741 :: uu____3743  in
        uu____3735 :: uu____3737  in
      uu____3729 :: uu____3731  in
    FStar_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu____3725
  
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs  ->
    let to_str uu____3814 =
      match uu____3814 with
      | (ts_t,ts_ty) ->
          let uu____3822 = tscheme_to_string ts_t  in
          let uu____3824 = tscheme_to_string ts_ty  in
          FStar_Util.format2 "(%s) : (%s)" uu____3822 uu____3824
       in
    let uu____3827 =
      let uu____3831 =
        FStar_Ident.string_of_lid combs.FStar_Syntax_Syntax.l_base_effect  in
      let uu____3833 =
        let uu____3837 = to_str combs.FStar_Syntax_Syntax.l_repr  in
        let uu____3839 =
          let uu____3843 = to_str combs.FStar_Syntax_Syntax.l_return  in
          let uu____3845 =
            let uu____3849 = to_str combs.FStar_Syntax_Syntax.l_bind  in
            let uu____3851 =
              let uu____3855 = to_str combs.FStar_Syntax_Syntax.l_subcomp  in
              let uu____3857 =
                let uu____3861 =
                  to_str combs.FStar_Syntax_Syntax.l_if_then_else  in
                [uu____3861]  in
              uu____3855 :: uu____3857  in
            uu____3849 :: uu____3851  in
          uu____3843 :: uu____3845  in
        uu____3837 :: uu____3839  in
      uu____3831 :: uu____3833  in
    FStar_Util.format
      "{\nl_base_effect = %s\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  }\n"
      uu____3827
  
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___14_3877  ->
    match uu___14_3877 with
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
          let uu____3910 =
            let uu____3912 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3912  in
          if uu____3910
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
               let uu____3933 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3933 (FStar_String.concat ",\n\t")
                in
             let eff_name =
               let uu____3950 = FStar_Syntax_Util.is_layered ed  in
               if uu____3950 then "layered_effect" else "new_effect"  in
             let uu____3958 =
               let uu____3962 =
                 let uu____3966 =
                   let uu____3970 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname  in
                   let uu____3972 =
                     let uu____3976 =
                       let uu____3978 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs
                          in
                       FStar_All.pipe_left enclose_universes uu____3978  in
                     let uu____3982 =
                       let uu____3986 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders
                          in
                       let uu____3989 =
                         let uu____3993 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature
                            in
                         let uu____3995 =
                           let uu____3999 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____4001 =
                             let uu____4005 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions
                                in
                             [uu____4005]  in
                           uu____3999 :: uu____4001  in
                         uu____3993 :: uu____3995  in
                       uu____3986 :: uu____3989  in
                     uu____3976 :: uu____3982  in
                   uu____3970 :: uu____3972  in
                 (if for_free then "_for_free " else "") :: uu____3966  in
               eff_name :: uu____3962  in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu____3958)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se  ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
        let uu____4057 = FStar_All.pipe_right ts_opt FStar_Util.must  in
        FStar_All.pipe_right uu____4057 tscheme_to_string
      else "<None>"  in
    let uu____4064 = lid_to_string se.FStar_Syntax_Syntax.source  in
    let uu____4066 = lid_to_string se.FStar_Syntax_Syntax.target  in
    let uu____4068 = tsopt_to_string se.FStar_Syntax_Syntax.lift  in
    let uu____4070 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp  in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____4064 uu____4066 uu____4068 uu____4070
  
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
          (lid,univs1,tps,k,uu____4105,uu____4106) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4122 = FStar_Options.print_universes ()  in
          if uu____4122
          then
            let uu____4126 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____4126 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____4135,uu____4136,uu____4137) ->
          let uu____4144 = FStar_Options.print_universes ()  in
          if uu____4144
          then
            let uu____4148 = univ_names_to_string univs1  in
            let uu____4150 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4148
              lid.FStar_Ident.str uu____4150
          else
            (let uu____4155 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____4155)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____4161 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4163 =
            let uu____4165 = FStar_Options.print_universes ()  in
            if uu____4165
            then
              let uu____4169 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____4169
            else ""  in
          let uu____4175 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4161
            lid.FStar_Ident.str uu____4163 uu____4175
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4181 = FStar_Options.print_universes ()  in
          if uu____4181
          then
            let uu____4185 = univ_names_to_string us  in
            let uu____4187 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____4185 uu____4187
          else
            (let uu____4192 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4192)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4196) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4202 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____4202
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4206) ->
          let uu____4215 =
            let uu____4217 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4217 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____4215
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4229 = FStar_Syntax_Util.is_dm4f ed  in
          eff_decl_to_string' uu____4229 x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____4241 = FStar_Options.print_universes ()  in
          if uu____4241
          then
            let uu____4245 =
              let uu____4250 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____4250  in
            (match uu____4245 with
             | (univs2,t) ->
                 let uu____4264 =
                   let uu____4269 =
                     let uu____4270 = FStar_Syntax_Subst.compress t  in
                     uu____4270.FStar_Syntax_Syntax.n  in
                   match uu____4269 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4299 -> failwith "impossible"  in
                 (match uu____4264 with
                  | (tps1,c1) ->
                      let uu____4308 = sli l  in
                      let uu____4310 = univ_names_to_string univs2  in
                      let uu____4312 = binders_to_string " " tps1  in
                      let uu____4315 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4308
                        uu____4310 uu____4312 uu____4315))
          else
            (let uu____4320 = sli l  in
             let uu____4322 = binders_to_string " " tps  in
             let uu____4325 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4320 uu____4322
               uu____4325)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4334 =
            let uu____4336 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4336  in
          let uu____4346 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4334 uu____4346
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4352 ->
        let uu____4355 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____4355 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____4372 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4372 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4383,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4385;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4387;
                       FStar_Syntax_Syntax.lbdef = uu____4388;
                       FStar_Syntax_Syntax.lbattrs = uu____4389;
                       FStar_Syntax_Syntax.lbpos = uu____4390;_}::[]),uu____4391)
        ->
        let uu____4414 = lbname_to_string lb  in
        let uu____4416 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4414 uu____4416
    | uu____4419 ->
        let uu____4420 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____4420 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4444 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4446 =
      let uu____4448 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4448 (FStar_String.concat "\n")  in
    let uu____4458 =
      let uu____4460 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4460 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4444
      uu____4446 uu____4458
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
           (let uu____4510 = f x  in
            FStar_Util.string_builder_append strb uu____4510);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4519 = f x1  in
                 FStar_Util.string_builder_append strb uu____4519)) xs;
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
           (let uu____4566 = f x  in
            FStar_Util.string_builder_append strb uu____4566);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4575 = f x1  in
                 FStar_Util.string_builder_append strb uu____4575)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____4597 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4597
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___15_4610  ->
    match uu___15_4610 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4626 =
          let uu____4628 =
            let uu____4630 =
              let uu____4632 =
                let uu____4634 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4634 (FStar_String.concat " ")  in
              Prims.op_Hat uu____4632 ")"  in
            Prims.op_Hat " " uu____4630  in
          Prims.op_Hat h uu____4628  in
        Prims.op_Hat "(" uu____4626
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4649 =
          let uu____4651 = emb_typ_to_string a  in
          let uu____4653 =
            let uu____4655 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____4655  in
          Prims.op_Hat uu____4651 uu____4653  in
        Prims.op_Hat "(" uu____4649
  