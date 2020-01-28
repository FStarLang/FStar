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
        let uu____1365 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____1365
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1369 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____1369
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1373 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____1373
    | FStar_Syntax_Syntax.Tm_uinst uu____1376 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1384 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1386 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1388,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1389;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1403,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1404;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1418 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1438 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1454 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1462 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1480 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1504 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1532 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1547 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1561,m) ->
        let uu____1599 = FStar_ST.op_Bang m  in
        (match uu____1599 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1635 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1641,m) ->
        let uu____1647 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____1647
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1651 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1654 =
      let uu____1656 = FStar_Options.ugly ()  in Prims.op_Negation uu____1656
       in
    if uu____1654
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1670 = FStar_Options.print_implicits ()  in
         if uu____1670 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1678 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1703,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1729,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____1731;
             FStar_Syntax_Syntax.rng = uu____1732;_}
           ->
           let uu____1743 =
             let uu____1745 =
               let uu____1747 = FStar_Thunk.force thunk1  in
               term_to_string uu____1747  in
             Prims.op_Hat uu____1745 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____1743
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1753 =
             let uu____1755 =
               let uu____1757 =
                 let uu____1758 =
                   let uu____1767 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1767  in
                 uu____1758 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1757  in
             Prims.op_Hat uu____1755 "]"  in
           Prims.op_Hat "[lazy:" uu____1753
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1836 =
                  match uu____1836 with
                  | (bv,t) ->
                      let uu____1844 = bv_to_string bv  in
                      let uu____1846 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1844 uu____1846
                   in
                let uu____1849 = term_to_string tm  in
                let uu____1851 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1849 uu____1851
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1860 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1860)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_pattern (uu____1864,ps)) ->
           let pats =
             let uu____1904 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1941 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1966  ->
                                 match uu____1966 with
                                 | (t1,uu____1975) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1941
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1904 (FStar_String.concat "\\/")  in
           let uu____1990 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1990
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic
            (FStar_Syntax_Syntax.Meta_monadic_bind m,t'))
           ->
           let uu____2004 = tag_of_term t  in
           let uu____2006 = sli m  in
           let uu____2008 = term_to_string t'  in
           let uu____2010 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____2004 uu____2006
             uu____2008 uu____2010
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic
            (FStar_Syntax_Syntax.Meta_polymonadic_bind (m,n1,p),t'))
           ->
           let uu____2026 = tag_of_term t  in
           let uu____2028 = sli m  in
           let uu____2030 = sli n1  in
           let uu____2032 = sli p  in
           let uu____2034 = term_to_string t'  in
           let uu____2036 = term_to_string t  in
           FStar_Util.format6 "(PolyMonadic-%s{((%s, %s) |> %s) %s} %s)"
             uu____2026 uu____2028 uu____2030 uu____2032 uu____2034
             uu____2036
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____2051 = tag_of_term t  in
           let uu____2053 = term_to_string t'  in
           let uu____2055 = sli m0  in
           let uu____2057 = sli m1  in
           let uu____2059 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2051
             uu____2053 uu____2055 uu____2057 uu____2059
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____2074 = FStar_Range.string_of_range r  in
           let uu____2076 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2074
             uu____2076
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2085 = lid_to_string l  in
           let uu____2087 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____2089 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2085 uu____2087
             uu____2089
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____2093) ->
           let uu____2098 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2098
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2102 = db_to_string x3  in
           let uu____2104 =
             let uu____2106 =
               let uu____2108 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____2108 ")"  in
             Prims.op_Hat ":(" uu____2106  in
           Prims.op_Hat uu____2102 uu____2104
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2115)) ->
           let uu____2130 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2130
           then ctx_uvar_to_string u
           else
             (let uu____2136 =
                let uu____2138 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2138  in
              Prims.op_Hat "?" uu____2136)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2161 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2161
           then
             let uu____2165 = ctx_uvar_to_string u  in
             let uu____2167 =
               let uu____2169 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2169 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2165 uu____2167
           else
             (let uu____2188 =
                let uu____2190 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2190  in
              Prims.op_Hat "?" uu____2188)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2197 = FStar_Options.print_universes ()  in
           if uu____2197
           then
             let uu____2201 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2201
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2229 = binders_to_string " -> " bs  in
           let uu____2232 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2229 uu____2232
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2264 = binders_to_string " " bs  in
                let uu____2267 = term_to_string t2  in
                let uu____2269 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2278 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2278)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2264 uu____2267
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____2269
            | uu____2282 ->
                let uu____2285 = binders_to_string " " bs  in
                let uu____2288 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2285 uu____2288)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2297 = bv_to_string xt  in
           let uu____2299 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2302 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2297 uu____2299 uu____2302
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2334 = term_to_string t  in
           let uu____2336 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2334 uu____2336
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2359 = lbs_to_string [] lbs  in
           let uu____2361 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2359 uu____2361
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2426 =
                   let uu____2428 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____2428
                     (FStar_Util.dflt "default")
                    in
                 let uu____2439 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2426 uu____2439
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2460 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2460
              in
           let uu____2463 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2463 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____2504 = term_to_string head1  in
           let uu____2506 =
             let uu____2508 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string)
                in
             FStar_Util.concat_l "\n\t|" uu____2508  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2504 uu____2506
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2526 = FStar_Options.print_universes ()  in
           if uu____2526
           then
             let uu____2530 = term_to_string t  in
             let uu____2532 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2530 uu____2532
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____2538  ->
    match uu____2538 with
    | (p,wopt,e) ->
        let uu____2560 = FStar_All.pipe_right p pat_to_string  in
        let uu____2563 =
          match wopt with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____2574 = FStar_All.pipe_right w term_to_string  in
              FStar_Util.format1 "when %s" uu____2574
           in
        let uu____2578 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format3 "%s %s -> %s" uu____2560 uu____2563 uu____2578

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2583 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2586 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2588 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2583 uu____2586
      uu____2588

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2591  ->
    match uu___5_2591 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2597 = FStar_Util.string_of_int i  in
        let uu____2599 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2597 uu____2599
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2606 = bv_to_string x  in
        let uu____2608 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2606 uu____2608
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2617 = bv_to_string x  in
        let uu____2619 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2617 uu____2619
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2626 = FStar_Util.string_of_int i  in
        let uu____2628 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2626 uu____2628
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2635 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2635

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2639 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2639 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2655 =
      let uu____2657 = FStar_Options.ugly ()  in Prims.op_Negation uu____2657
       in
    if uu____2655
    then
      let e =
        let uu____2662 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2662  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2691 = fv_to_string l  in
           let uu____2693 =
             let uu____2695 =
               FStar_List.map
                 (fun uu____2709  ->
                    match uu____2709 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2695 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2691 uu____2693
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2734) ->
           let uu____2739 = FStar_Options.print_bound_var_types ()  in
           if uu____2739
           then
             let uu____2743 = bv_to_string x1  in
             let uu____2745 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2743 uu____2745
           else
             (let uu____2750 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2750)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2754 = FStar_Options.print_bound_var_types ()  in
           if uu____2754
           then
             let uu____2758 = bv_to_string x1  in
             let uu____2760 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2758 uu____2760
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2767 = FStar_Options.print_bound_var_types ()  in
           if uu____2767
           then
             let uu____2771 = bv_to_string x1  in
             let uu____2773 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2771 uu____2773
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2782 = quals_to_string' quals  in
      let uu____2784 =
        let uu____2786 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2806 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2808 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2810 =
                    let uu____2812 = FStar_Options.print_universes ()  in
                    if uu____2812
                    then
                      let uu____2816 =
                        let uu____2818 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____2818 ">"  in
                      Prims.op_Hat "<" uu____2816
                    else ""  in
                  let uu____2825 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2827 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2806
                    uu____2808 uu____2810 uu____2825 uu____2827))
           in
        FStar_Util.concat_l "\n and " uu____2786  in
      FStar_Util.format3 "%slet %s %s" uu____2782
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2784

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2842  ->
    match uu___6_2842 with
    | [] -> ""
    | tms ->
        let uu____2850 =
          let uu____2852 =
            FStar_List.map
              (fun t  ->
                 let uu____2860 = term_to_string t  in paren uu____2860) tms
             in
          FStar_All.pipe_right uu____2852 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2850

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___7_2869  ->
      match uu___7_2869 with
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
          let uu____2887 =
            let uu____2889 = term_to_string t  in
            Prims.op_Hat uu____2889 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____2887
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
      let uu____2907 =
        let uu____2909 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2909  in
      if uu____2907
      then
        let uu____2913 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2913 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
        (let uu____2924 = b  in
         match uu____2924 with
         | (a,imp) ->
             let uu____2938 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2938
             then
               let uu____2942 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat "_:" uu____2942
             else
               (let uu____2947 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2950 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2950)
                   in
                if uu____2947
                then
                  let uu____2954 = nm_to_string a  in
                  imp_to_string uu____2954 imp
                else
                  (let uu____2958 =
                     let uu____2960 = nm_to_string a  in
                     let uu____2962 =
                       let uu____2964 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____2964  in
                     Prims.op_Hat uu____2960 uu____2962  in
                   imp_to_string uu____2958 imp)))

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
        let uu____2983 = FStar_Options.print_implicits ()  in
        if uu____2983 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2994 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2994 (FStar_String.concat sep)
      else
        (let uu____3022 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____3022 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_3036  ->
    match uu___8_3036 with
    | (a,imp) ->
        let uu____3050 = term_to_string a  in imp_to_string uu____3050 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____3062 = FStar_Options.print_implicits ()  in
      if uu____3062 then args else filter_imp args  in
    let uu____3077 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____3077 (FStar_String.concat " ")

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____3105 =
      let uu____3107 = FStar_Options.ugly ()  in Prims.op_Negation uu____3107
       in
    if uu____3105
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____3128 =
             let uu____3129 = FStar_Syntax_Subst.compress t  in
             uu____3129.FStar_Syntax_Syntax.n  in
           (match uu____3128 with
            | FStar_Syntax_Syntax.Tm_type uu____3133 when
                let uu____3134 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3134 -> term_to_string t
            | uu____3136 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3139 = univ_to_string u  in
                     let uu____3141 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3139 uu____3141
                 | uu____3144 ->
                     let uu____3147 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3147))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3160 =
             let uu____3161 = FStar_Syntax_Subst.compress t  in
             uu____3161.FStar_Syntax_Syntax.n  in
           (match uu____3160 with
            | FStar_Syntax_Syntax.Tm_type uu____3165 when
                let uu____3166 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3166 -> term_to_string t
            | uu____3168 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3171 = univ_to_string u  in
                     let uu____3173 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3171 uu____3173
                 | uu____3176 ->
                     let uu____3179 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3179))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3185 = FStar_Options.print_effect_args ()  in
             if uu____3185
             then
               let uu____3189 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3191 =
                 let uu____3193 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3193 (FStar_String.concat ", ")
                  in
               let uu____3208 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3210 =
                 let uu____3212 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3212 (FStar_String.concat ", ")
                  in
               let uu____3239 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3189
                 uu____3191 uu____3208 uu____3210 uu____3239
             else
               (let uu____3244 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3250  ->
                           match uu___9_3250 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3253 -> false)))
                    &&
                    (let uu____3256 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3256)
                   in
                if uu____3244
                then
                  let uu____3260 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3260
                else
                  (let uu____3265 =
                     ((let uu____3269 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3269) &&
                        (let uu____3272 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3272))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____3265
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3278 =
                        (let uu____3282 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3282) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3288  ->
                                   match uu___10_3288 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3291 -> false)))
                         in
                      if uu____3278
                      then
                        let uu____3295 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3295
                      else
                        (let uu____3300 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3302 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3300 uu____3302))))
              in
           let dec =
             let uu____3307 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3320  ->
                       match uu___11_3320 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3327 =
                             let uu____3329 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3329
                              in
                           [uu____3327]
                       | uu____3334 -> []))
                in
             FStar_All.pipe_right uu____3307 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____3353 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_3363  ->
    match uu___12_3363 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____3365,ps) ->
        let pats =
          let uu____3401 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3438 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3463  ->
                              match uu____3463 with
                              | (t,uu____3472) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3438
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3401 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3489 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3489
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3494) ->
        let uu____3499 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3499
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic
        (FStar_Syntax_Syntax.Meta_monadic_bind m,t) ->
        let uu____3510 = sli m  in
        let uu____3512 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3510 uu____3512
    | FStar_Syntax_Syntax.Meta_monadic
        (FStar_Syntax_Syntax.Meta_polymonadic_bind (m,n1,p),t) ->
        let uu____3523 = sli m  in
        let uu____3525 = sli n1  in
        let uu____3527 = sli p  in
        let uu____3529 = term_to_string t  in
        FStar_Util.format4 "{Meta_polymonadic(((%s, %s) |> %s) @ %s)}"
          uu____3523 uu____3525 uu____3527 uu____3529
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3539 = sli m  in
        let uu____3541 = sli m'  in
        let uu____3543 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3539
          uu____3541 uu____3543

let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq  -> aqual_to_string' "" aq 
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____3566 = FStar_Options.ugly ()  in
      if uu____3566
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
      let uu____3588 = FStar_Options.ugly ()  in
      if uu____3588
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
      let uu____3609 = b  in
      match uu____3609 with
      | (a,imp) ->
          let n1 =
            let uu____3617 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3617
            then FStar_Util.JsonNull
            else
              (let uu____3622 =
                 let uu____3624 = nm_to_string a  in
                 imp_to_string uu____3624 imp  in
               FStar_Util.JsonStr uu____3622)
             in
          let t =
            let uu____3627 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3627  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____3659 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3659
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3677 = FStar_Options.print_universes ()  in
    if uu____3677 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3693 =
      let uu____3695 = FStar_Options.ugly ()  in Prims.op_Negation uu____3695
       in
    if uu____3693
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
      (let uu____3705 = s  in
       match uu____3705 with
       | (us,t) ->
           let uu____3717 =
             let uu____3719 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3719  in
           let uu____3723 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3717 uu____3723)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3733 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3735 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3738 =
      let uu____3740 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3740  in
    let uu____3744 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3746 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3733 uu____3735 uu____3738
      uu____3744 uu____3746
  
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs  ->
    let tscheme_opt_to_string uu___13_3764 =
      match uu___13_3764 with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None  -> "None"  in
    let uu____3770 =
      let uu____3774 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____3776 =
        let uu____3780 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp
           in
        let uu____3782 =
          let uu____3786 =
            tscheme_to_string combs.FStar_Syntax_Syntax.stronger  in
          let uu____3788 =
            let uu____3792 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else  in
            let uu____3794 =
              let uu____3798 =
                tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp  in
              let uu____3800 =
                let uu____3804 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp  in
                let uu____3806 =
                  let uu____3810 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial  in
                  let uu____3812 =
                    let uu____3816 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr
                       in
                    let uu____3818 =
                      let uu____3822 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr
                         in
                      let uu____3824 =
                        let uu____3828 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr
                           in
                        [uu____3828]  in
                      uu____3822 :: uu____3824  in
                    uu____3816 :: uu____3818  in
                  uu____3810 :: uu____3812  in
                uu____3804 :: uu____3806  in
              uu____3798 :: uu____3800  in
            uu____3792 :: uu____3794  in
          uu____3786 :: uu____3788  in
        uu____3780 :: uu____3782  in
      uu____3774 :: uu____3776  in
    FStar_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu____3770
  
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs  ->
    let to_str uu____3859 =
      match uu____3859 with
      | (ts_t,ts_ty) ->
          let uu____3867 = tscheme_to_string ts_t  in
          let uu____3869 = tscheme_to_string ts_ty  in
          FStar_Util.format2 "(%s) : (%s)" uu____3867 uu____3869
       in
    let uu____3872 =
      let uu____3876 =
        FStar_Ident.string_of_lid combs.FStar_Syntax_Syntax.l_base_effect  in
      let uu____3878 =
        let uu____3882 = to_str combs.FStar_Syntax_Syntax.l_repr  in
        let uu____3884 =
          let uu____3888 = to_str combs.FStar_Syntax_Syntax.l_return  in
          let uu____3890 =
            let uu____3894 = to_str combs.FStar_Syntax_Syntax.l_bind  in
            let uu____3896 =
              let uu____3900 = to_str combs.FStar_Syntax_Syntax.l_subcomp  in
              let uu____3902 =
                let uu____3906 =
                  to_str combs.FStar_Syntax_Syntax.l_if_then_else  in
                [uu____3906]  in
              uu____3900 :: uu____3902  in
            uu____3894 :: uu____3896  in
          uu____3888 :: uu____3890  in
        uu____3882 :: uu____3884  in
      uu____3876 :: uu____3878  in
    FStar_Util.format
      "{\nl_base_effect = %s\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  }\n"
      uu____3872
  
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___14_3922  ->
    match uu___14_3922 with
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
          let uu____3955 =
            let uu____3957 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3957  in
          if uu____3955
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
               let uu____3978 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3978 (FStar_String.concat ",\n\t")
                in
             let eff_name =
               let uu____3995 = FStar_Syntax_Util.is_layered ed  in
               if uu____3995 then "layered_effect" else "new_effect"  in
             let uu____4003 =
               let uu____4007 =
                 let uu____4011 =
                   let uu____4015 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname  in
                   let uu____4017 =
                     let uu____4021 =
                       let uu____4023 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs
                          in
                       FStar_All.pipe_left enclose_universes uu____4023  in
                     let uu____4027 =
                       let uu____4031 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders
                          in
                       let uu____4034 =
                         let uu____4038 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature
                            in
                         let uu____4040 =
                           let uu____4044 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____4046 =
                             let uu____4050 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions
                                in
                             [uu____4050]  in
                           uu____4044 :: uu____4046  in
                         uu____4038 :: uu____4040  in
                       uu____4031 :: uu____4034  in
                     uu____4021 :: uu____4027  in
                   uu____4015 :: uu____4017  in
                 (if for_free then "_for_free " else "") :: uu____4011  in
               eff_name :: uu____4007  in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu____4003)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se  ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
        let uu____4102 = FStar_All.pipe_right ts_opt FStar_Util.must  in
        FStar_All.pipe_right uu____4102 tscheme_to_string
      else "<None>"  in
    let uu____4109 = lid_to_string se.FStar_Syntax_Syntax.source  in
    let uu____4111 = lid_to_string se.FStar_Syntax_Syntax.target  in
    let uu____4113 = tsopt_to_string se.FStar_Syntax_Syntax.lift  in
    let uu____4115 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp  in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____4109 uu____4111 uu____4113 uu____4115
  
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
          (lid,univs1,tps,k,uu____4150,uu____4151) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4167 = FStar_Options.print_universes ()  in
          if uu____4167
          then
            let uu____4171 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____4171 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____4180,uu____4181,uu____4182) ->
          let uu____4189 = FStar_Options.print_universes ()  in
          if uu____4189
          then
            let uu____4193 = univ_names_to_string univs1  in
            let uu____4195 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4193
              lid.FStar_Ident.str uu____4195
          else
            (let uu____4200 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____4200)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____4206 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4208 =
            let uu____4210 = FStar_Options.print_universes ()  in
            if uu____4210
            then
              let uu____4214 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____4214
            else ""  in
          let uu____4220 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4206
            lid.FStar_Ident.str uu____4208 uu____4220
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4226 = FStar_Options.print_universes ()  in
          if uu____4226
          then
            let uu____4230 = univ_names_to_string us  in
            let uu____4232 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____4230 uu____4232
          else
            (let uu____4237 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4237)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4241) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4247 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____4247
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4251) ->
          let uu____4260 =
            let uu____4262 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4262 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____4260
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4274 = FStar_Syntax_Util.is_dm4f ed  in
          eff_decl_to_string' uu____4274 x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____4286 = FStar_Options.print_universes ()  in
          if uu____4286
          then
            let uu____4290 =
              let uu____4295 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____4295  in
            (match uu____4290 with
             | (univs2,t) ->
                 let uu____4309 =
                   let uu____4314 =
                     let uu____4315 = FStar_Syntax_Subst.compress t  in
                     uu____4315.FStar_Syntax_Syntax.n  in
                   match uu____4314 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4344 -> failwith "impossible"  in
                 (match uu____4309 with
                  | (tps1,c1) ->
                      let uu____4353 = sli l  in
                      let uu____4355 = univ_names_to_string univs2  in
                      let uu____4357 = binders_to_string " " tps1  in
                      let uu____4360 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4353
                        uu____4355 uu____4357 uu____4360))
          else
            (let uu____4365 = sli l  in
             let uu____4367 = binders_to_string " " tps  in
             let uu____4370 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4365 uu____4367
               uu____4370)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4379 =
            let uu____4381 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4381  in
          let uu____4391 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4379 uu____4391
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n1,p,t,ty) ->
          let uu____4399 = FStar_Ident.string_of_lid m  in
          let uu____4401 = FStar_Ident.string_of_lid n1  in
          let uu____4403 = FStar_Ident.string_of_lid p  in
          let uu____4405 = tscheme_to_string t  in
          let uu____4407 = tscheme_to_string ty  in
          FStar_Util.format5 "polymonadic_bind (%s, %s) |> %s = (%s, %s)"
            uu____4399 uu____4401 uu____4403 uu____4405 uu____4407
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4413 ->
        let uu____4416 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____4416 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____4433 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4433 msg
  
let (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4444,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4446;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4448;
                       FStar_Syntax_Syntax.lbdef = uu____4449;
                       FStar_Syntax_Syntax.lbattrs = uu____4450;
                       FStar_Syntax_Syntax.lbpos = uu____4451;_}::[]),uu____4452)
        ->
        let uu____4475 = lbname_to_string lb  in
        let uu____4477 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4475 uu____4477
    | uu____4480 ->
        let uu____4481 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____4481 (FStar_String.concat ", ")
  
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4505 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4507 =
      let uu____4509 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4509 (FStar_String.concat "\n")  in
    let uu____4519 =
      let uu____4521 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4521 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4505
      uu____4507 uu____4519
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
           (let uu____4571 = f x  in
            FStar_Util.string_builder_append strb uu____4571);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4580 = f x1  in
                 FStar_Util.string_builder_append strb uu____4580)) xs;
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
           (let uu____4627 = f x  in
            FStar_Util.string_builder_append strb uu____4627);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4636 = f x1  in
                 FStar_Util.string_builder_append strb uu____4636)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____4658 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4658
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___15_4671  ->
    match uu___15_4671 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4687 =
          let uu____4689 =
            let uu____4691 =
              let uu____4693 =
                let uu____4695 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4695 (FStar_String.concat " ")  in
              Prims.op_Hat uu____4693 ")"  in
            Prims.op_Hat " " uu____4691  in
          Prims.op_Hat h uu____4689  in
        Prims.op_Hat "(" uu____4687
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4710 =
          let uu____4712 = emb_typ_to_string a  in
          let uu____4714 =
            let uu____4716 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____4716  in
          Prims.op_Hat uu____4712 uu____4714  in
        Prims.op_Hat "(" uu____4710
  