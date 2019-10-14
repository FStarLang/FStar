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
<<<<<<< HEAD
        let uu____1374 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____1374
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1378 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____1378
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1382 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____1382
    | FStar_Syntax_Syntax.Tm_uinst uu____1385 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1393 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1395 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1397,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1398;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1412,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1413;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1427 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1447 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1463 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1471 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1489 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1513 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1541 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1556 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1570,m) ->
        let uu____1608 = FStar_ST.op_Bang m  in
        (match uu____1608 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1644 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1650,m) ->
        let uu____1656 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____1656
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1660 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1663 =
      let uu____1665 = FStar_Options.ugly ()  in Prims.op_Negation uu____1665
       in
    if uu____1663
=======
        let uu____1384 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____1384
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1388 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____1388
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1392 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____1392
    | FStar_Syntax_Syntax.Tm_uinst uu____1395 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1403 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1405 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1407,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1408;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1422,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1423;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1437 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1457 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1473 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1481 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1499 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1523 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1551 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1566 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1580,m) ->
        let uu____1618 = FStar_ST.op_Bang m  in
        (match uu____1618 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1654 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1660,m) ->
        let uu____1666 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____1666
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1670 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1673 =
      let uu____1675 = FStar_Options.ugly ()  in Prims.op_Negation uu____1675
       in
    if uu____1673
>>>>>>> snap
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
<<<<<<< HEAD
         let uu____1679 = FStar_Options.print_implicits ()  in
         if uu____1679 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1687 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1712,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1738,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____1740;
             FStar_Syntax_Syntax.rng = uu____1741;_}
           ->
           let uu____1752 =
             let uu____1754 =
               let uu____1756 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____1756  in
             Prims.op_Hat uu____1754 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____1752
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1762 =
             let uu____1764 =
               let uu____1766 =
                 let uu____1767 =
                   let uu____1776 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1776  in
                 uu____1767 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1766  in
             Prims.op_Hat uu____1764 "]"  in
           Prims.op_Hat "[lazy:" uu____1762
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1845 =
                  match uu____1845 with
                  | (bv,t) ->
                      let uu____1853 = bv_to_string bv  in
                      let uu____1855 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1853 uu____1855
                   in
                let uu____1858 = term_to_string tm  in
                let uu____1860 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1858 uu____1860
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1869 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1869)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_pattern (uu____1873,ps)) ->
           let pats =
             let uu____1913 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1950 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1975  ->
                                 match uu____1975 with
                                 | (t1,uu____1984) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1950
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1913 (FStar_String.concat "\\/")  in
           let uu____1999 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1999
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____2013 = tag_of_term t  in
           let uu____2015 = sli m  in
           let uu____2017 = term_to_string t'  in
           let uu____2019 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____2013 uu____2015
             uu____2017 uu____2019
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____2034 = tag_of_term t  in
           let uu____2036 = term_to_string t'  in
           let uu____2038 = sli m0  in
           let uu____2040 = sli m1  in
           let uu____2042 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2034
             uu____2036 uu____2038 uu____2040 uu____2042
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____2057 = FStar_Range.string_of_range r  in
           let uu____2059 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2057
             uu____2059
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2068 = lid_to_string l  in
           let uu____2070 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____2072 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2068 uu____2070
             uu____2072
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____2076) ->
           let uu____2081 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2081
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2085 = db_to_string x3  in
           let uu____2087 =
             let uu____2089 =
               let uu____2091 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____2091 ")"  in
             Prims.op_Hat ":(" uu____2089  in
           Prims.op_Hat uu____2085 uu____2087
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2098)) ->
           let uu____2113 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2113
           then ctx_uvar_to_string u
           else
             (let uu____2119 =
                let uu____2121 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2121  in
              Prims.op_Hat "?" uu____2119)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2144 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2144
           then
             let uu____2148 = ctx_uvar_to_string u  in
             let uu____2150 =
               let uu____2152 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2152 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2148 uu____2150
           else
             (let uu____2171 =
                let uu____2173 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2173  in
              Prims.op_Hat "?" uu____2171)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2180 = FStar_Options.print_universes ()  in
           if uu____2180
           then
             let uu____2184 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2184
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2212 = binders_to_string " -> " bs  in
           let uu____2215 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2212 uu____2215
=======
         let uu____1689 = FStar_Options.print_implicits ()  in
         if uu____1689 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1697 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1722,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1748,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____1750;
             FStar_Syntax_Syntax.rng = uu____1751;_}
           ->
           let uu____1762 =
             let uu____1764 =
               let uu____1766 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____1766  in
             Prims.op_Hat uu____1764 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____1762
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1772 =
             let uu____1774 =
               let uu____1776 =
                 let uu____1777 =
                   let uu____1786 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1786  in
                 uu____1777 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1776  in
             Prims.op_Hat uu____1774 "]"  in
           Prims.op_Hat "[lazy:" uu____1772
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1855 =
                  match uu____1855 with
                  | (bv,t) ->
                      let uu____1863 = bv_to_string bv  in
                      let uu____1865 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1863 uu____1865
                   in
                let uu____1868 = term_to_string tm  in
                let uu____1870 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1868 uu____1870
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1879 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1879)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_pattern (uu____1883,ps)) ->
           let pats =
             let uu____1923 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1960 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1985  ->
                                 match uu____1985 with
                                 | (t1,uu____1994) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1960
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1923 (FStar_String.concat "\\/")  in
           let uu____2009 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____2009
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____2023 = tag_of_term t  in
           let uu____2025 = sli m  in
           let uu____2027 = term_to_string t'  in
           let uu____2029 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____2023 uu____2025
             uu____2027 uu____2029
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____2044 = tag_of_term t  in
           let uu____2046 = term_to_string t'  in
           let uu____2048 = sli m0  in
           let uu____2050 = sli m1  in
           let uu____2052 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2044
             uu____2046 uu____2048 uu____2050 uu____2052
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____2067 = FStar_Range.string_of_range r  in
           let uu____2069 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2067
             uu____2069
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2078 = lid_to_string l  in
           let uu____2080 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____2082 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2078 uu____2080
             uu____2082
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____2086) ->
           let uu____2091 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2091
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2095 = db_to_string x3  in
           let uu____2097 =
             let uu____2099 =
               let uu____2101 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____2101 ")"  in
             Prims.op_Hat ":(" uu____2099  in
           Prims.op_Hat uu____2095 uu____2097
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2108)) ->
           let uu____2123 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2123
           then ctx_uvar_to_string u
           else
             (let uu____2129 =
                let uu____2131 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2131  in
              Prims.op_Hat "?" uu____2129)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2154 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2154
           then
             let uu____2158 = ctx_uvar_to_string u  in
             let uu____2160 =
               let uu____2162 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2162 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2158 uu____2160
           else
             (let uu____2181 =
                let uu____2183 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2183  in
              Prims.op_Hat "?" uu____2181)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2190 = FStar_Options.print_universes ()  in
           if uu____2190
           then
             let uu____2194 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2194
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2222 = binders_to_string " -> " bs  in
           let uu____2225 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2222 uu____2225
>>>>>>> snap
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
<<<<<<< HEAD
                let uu____2247 = binders_to_string " " bs  in
                let uu____2250 = term_to_string t2  in
                let uu____2252 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2261 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2261)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2247 uu____2250
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____2252
            | uu____2265 ->
                let uu____2268 = binders_to_string " " bs  in
                let uu____2271 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2268 uu____2271)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2280 = bv_to_string xt  in
           let uu____2282 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2285 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2280 uu____2282 uu____2285
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2317 = term_to_string t  in
           let uu____2319 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2317 uu____2319
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2342 = lbs_to_string [] lbs  in
           let uu____2344 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2342 uu____2344
=======
                let uu____2257 = binders_to_string " " bs  in
                let uu____2260 = term_to_string t2  in
                let uu____2262 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2271 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2271)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2257 uu____2260
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____2262
            | uu____2275 ->
                let uu____2278 = binders_to_string " " bs  in
                let uu____2281 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2278 uu____2281)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2290 = bv_to_string xt  in
           let uu____2292 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2295 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2290 uu____2292 uu____2295
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2327 = term_to_string t  in
           let uu____2329 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2327 uu____2329
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2352 = lbs_to_string [] lbs  in
           let uu____2354 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2352 uu____2354
>>>>>>> snap
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
<<<<<<< HEAD
                 let uu____2409 =
                   let uu____2411 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____2411
                     (FStar_Util.dflt "default")
                    in
                 let uu____2422 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2409 uu____2422
=======
                 let uu____2419 =
                   let uu____2421 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____2421
                     (FStar_Util.dflt "default")
                    in
                 let uu____2432 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2419 uu____2432
>>>>>>> snap
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
<<<<<<< HEAD
                 let uu____2443 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2443
              in
           let uu____2446 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2446 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____2487 = term_to_string head1  in
           let uu____2489 =
             let uu____2491 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____2524  ->
                       match uu____2524 with
                       | (p,wopt,e) ->
                           let uu____2541 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____2544 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____2549 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____2549
                              in
                           let uu____2553 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____2541
                             uu____2544 uu____2553))
                in
             FStar_Util.concat_l "\n\t|" uu____2491  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2487 uu____2489
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2565 = FStar_Options.print_universes ()  in
           if uu____2565
           then
             let uu____2569 = term_to_string t  in
             let uu____2571 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2569 uu____2571
=======
                 let uu____2453 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2453
              in
           let uu____2456 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2456 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____2497 = term_to_string head1  in
           let uu____2499 =
             let uu____2501 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string)
                in
             FStar_Util.concat_l "\n\t|" uu____2501  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2497 uu____2499
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2519 = FStar_Options.print_universes ()  in
           if uu____2519
           then
             let uu____2523 = term_to_string t  in
             let uu____2525 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2523 uu____2525
>>>>>>> snap
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____2531  ->
    match uu____2531 with
    | (p,wopt,e) ->
        let uu____2553 = FStar_All.pipe_right p pat_to_string  in
        let uu____2556 =
          match wopt with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____2567 = FStar_All.pipe_right w term_to_string  in
              FStar_Util.format1 "when %s" uu____2567
           in
        let uu____2571 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format3 "%s %s -> %s" uu____2553 uu____2556 uu____2571

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
<<<<<<< HEAD
    let uu____2578 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2581 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2583 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2578 uu____2581
      uu____2583

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2586  ->
    match uu___5_2586 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2592 = FStar_Util.string_of_int i  in
        let uu____2594 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2592 uu____2594
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2601 = bv_to_string x  in
        let uu____2603 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2601 uu____2603
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2612 = bv_to_string x  in
        let uu____2614 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2612 uu____2614
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2621 = FStar_Util.string_of_int i  in
        let uu____2623 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2621 uu____2623
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2630 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2630

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2634 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2634 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2650 =
      let uu____2652 = FStar_Options.ugly ()  in Prims.op_Negation uu____2652
       in
    if uu____2650
    then
      let e =
        let uu____2657 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2657  in
=======
    let uu____2576 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2579 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2581 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2576 uu____2579
      uu____2581

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2584  ->
    match uu___5_2584 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2590 = FStar_Util.string_of_int i  in
        let uu____2592 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2590 uu____2592
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2599 = bv_to_string x  in
        let uu____2601 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2599 uu____2601
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2610 = bv_to_string x  in
        let uu____2612 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2610 uu____2612
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2619 = FStar_Util.string_of_int i  in
        let uu____2621 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2619 uu____2621
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2628 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2628

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2632 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2632 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2648 =
      let uu____2650 = FStar_Options.ugly ()  in Prims.op_Negation uu____2650
       in
    if uu____2648
    then
      let e =
        let uu____2655 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2655  in
>>>>>>> snap
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
<<<<<<< HEAD
           let uu____2686 = fv_to_string l  in
           let uu____2688 =
             let uu____2690 =
               FStar_List.map
                 (fun uu____2704  ->
                    match uu____2704 with
=======
           let uu____2684 = fv_to_string l  in
           let uu____2686 =
             let uu____2688 =
               FStar_List.map
                 (fun uu____2702  ->
                    match uu____2702 with
>>>>>>> snap
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
<<<<<<< HEAD
             FStar_All.pipe_right uu____2690 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2686 uu____2688
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2729) ->
           let uu____2734 = FStar_Options.print_bound_var_types ()  in
           if uu____2734
           then
             let uu____2738 = bv_to_string x1  in
             let uu____2740 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2738 uu____2740
           else
             (let uu____2745 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2745)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2749 = FStar_Options.print_bound_var_types ()  in
           if uu____2749
           then
             let uu____2753 = bv_to_string x1  in
             let uu____2755 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2753 uu____2755
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2762 = FStar_Options.print_bound_var_types ()  in
           if uu____2762
           then
             let uu____2766 = bv_to_string x1  in
             let uu____2768 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2766 uu____2768
=======
             FStar_All.pipe_right uu____2688 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2684 uu____2686
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2727) ->
           let uu____2732 = FStar_Options.print_bound_var_types ()  in
           if uu____2732
           then
             let uu____2736 = bv_to_string x1  in
             let uu____2738 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2736 uu____2738
           else
             (let uu____2743 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2743)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2747 = FStar_Options.print_bound_var_types ()  in
           if uu____2747
           then
             let uu____2751 = bv_to_string x1  in
             let uu____2753 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2751 uu____2753
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2760 = FStar_Options.print_bound_var_types ()  in
           if uu____2760
           then
             let uu____2764 = bv_to_string x1  in
             let uu____2766 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2764 uu____2766
>>>>>>> snap
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
<<<<<<< HEAD
      let uu____2777 = quals_to_string' quals  in
      let uu____2779 =
        let uu____2781 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2801 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2803 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2805 =
                    let uu____2807 = FStar_Options.print_universes ()  in
                    if uu____2807
                    then
                      let uu____2811 =
                        let uu____2813 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____2813 ">"  in
                      Prims.op_Hat "<" uu____2811
                    else ""  in
                  let uu____2820 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2822 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2801
                    uu____2803 uu____2805 uu____2820 uu____2822))
           in
        FStar_Util.concat_l "\n and " uu____2781  in
      FStar_Util.format3 "%slet %s %s" uu____2777
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2779

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2837  ->
    match uu___6_2837 with
    | [] -> ""
    | tms ->
        let uu____2845 =
          let uu____2847 =
            FStar_List.map
              (fun t  ->
                 let uu____2855 = term_to_string t  in paren uu____2855) tms
             in
          FStar_All.pipe_right uu____2847 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2845
=======
      let uu____2775 = quals_to_string' quals  in
      let uu____2777 =
        let uu____2779 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2799 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2801 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2803 =
                    let uu____2805 = FStar_Options.print_universes ()  in
                    if uu____2805
                    then
                      let uu____2809 =
                        let uu____2811 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____2811 ">"  in
                      Prims.op_Hat "<" uu____2809
                    else ""  in
                  let uu____2818 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2820 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2799
                    uu____2801 uu____2803 uu____2818 uu____2820))
           in
        FStar_Util.concat_l "\n and " uu____2779  in
      FStar_Util.format3 "%slet %s %s" uu____2775
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2777

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2835  ->
    match uu___6_2835 with
    | [] -> ""
    | tms ->
        let uu____2843 =
          let uu____2845 =
            FStar_List.map
              (fun t  ->
                 let uu____2853 = term_to_string t  in paren uu____2853) tms
             in
          FStar_All.pipe_right uu____2845 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2843

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2862 = FStar_Options.print_effect_args ()  in
    if uu____2862
    then
      let uu____2866 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2866
    else
      (let uu____2869 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2871 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2869 uu____2871)
>>>>>>> snap

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
<<<<<<< HEAD
    fun uu___7_2864  ->
      match uu___7_2864 with
=======
    fun uu___7_2875  ->
      match uu___7_2875 with
>>>>>>> snap
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
<<<<<<< HEAD
          let uu____2882 =
            let uu____2884 = term_to_string t  in
            Prims.op_Hat uu____2884 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____2882
=======
          let uu____2893 =
            let uu____2895 = term_to_string t  in
            Prims.op_Hat uu____2895 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____2893
>>>>>>> snap
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
<<<<<<< HEAD
      let uu____2904 =
        let uu____2906 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2906  in
      if uu____2904
      then
        let uu____2910 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2910 with
=======
      let uu____2915 =
        let uu____2917 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2917  in
      if uu____2915
      then
        let uu____2921 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2921 with
>>>>>>> snap
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
<<<<<<< HEAD
        (let uu____2921 = b  in
         match uu____2921 with
         | (a,imp) ->
             let uu____2935 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2935
             then
               let uu____2939 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat "_:" uu____2939
             else
               (let uu____2944 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2947 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2947)
                   in
                if uu____2944
                then
                  let uu____2951 = nm_to_string a  in
                  imp_to_string uu____2951 imp
                else
                  (let uu____2955 =
                     let uu____2957 = nm_to_string a  in
                     let uu____2959 =
                       let uu____2961 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____2961  in
                     Prims.op_Hat uu____2957 uu____2959  in
                   imp_to_string uu____2955 imp)))
=======
        (let uu____2932 = b  in
         match uu____2932 with
         | (a,imp) ->
             let uu____2946 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2946
             then
               let uu____2950 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat "_:" uu____2950
             else
               (let uu____2955 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2958 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2958)
                   in
                if uu____2955
                then
                  let uu____2962 = nm_to_string a  in
                  imp_to_string uu____2962 imp
                else
                  (let uu____2966 =
                     let uu____2968 = nm_to_string a  in
                     let uu____2970 =
                       let uu____2972 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____2972  in
                     Prims.op_Hat uu____2968 uu____2970  in
                   imp_to_string uu____2966 imp)))
>>>>>>> snap

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
<<<<<<< HEAD
        let uu____2980 = FStar_Options.print_implicits ()  in
        if uu____2980 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2991 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2991 (FStar_String.concat sep)
      else
        (let uu____3019 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____3019 (FStar_String.concat sep))
=======
        let uu____2991 = FStar_Options.print_implicits ()  in
        if uu____2991 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____3002 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____3002 (FStar_String.concat sep)
      else
        (let uu____3030 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____3030 (FStar_String.concat sep))
>>>>>>> snap

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
<<<<<<< HEAD
  fun uu___8_3033  ->
    match uu___8_3033 with
    | (a,imp) ->
        let uu____3047 = term_to_string a  in imp_to_string uu____3047 imp
=======
  fun uu___8_3044  ->
    match uu___8_3044 with
    | (a,imp) ->
        let uu____3058 = term_to_string a  in imp_to_string uu____3058 imp
>>>>>>> snap

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
<<<<<<< HEAD
      let uu____3059 = FStar_Options.print_implicits ()  in
      if uu____3059 then args else filter_imp args  in
    let uu____3074 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____3074 (FStar_String.concat " ")
=======
      let uu____3070 = FStar_Options.print_implicits ()  in
      if uu____3070 then args else filter_imp args  in
    let uu____3085 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____3085 (FStar_String.concat " ")
>>>>>>> snap

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
<<<<<<< HEAD
      let uu____3103 = FStar_Options.ugly ()  in
      if uu____3103
=======
      let uu____3114 = FStar_Options.ugly ()  in
      if uu____3114
>>>>>>> snap
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
<<<<<<< HEAD
    let uu____3114 =
      let uu____3116 = FStar_Options.ugly ()  in Prims.op_Negation uu____3116
       in
    if uu____3114
=======
    let uu____3125 =
      let uu____3127 = FStar_Options.ugly ()  in Prims.op_Negation uu____3127
       in
    if uu____3125
>>>>>>> snap
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
<<<<<<< HEAD
           let uu____3137 =
             let uu____3138 = FStar_Syntax_Subst.compress t  in
             uu____3138.FStar_Syntax_Syntax.n  in
           (match uu____3137 with
            | FStar_Syntax_Syntax.Tm_type uu____3142 when
                let uu____3143 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3143 -> term_to_string t
            | uu____3145 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3148 = univ_to_string u  in
                     let uu____3150 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3148 uu____3150
                 | uu____3153 ->
                     let uu____3156 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3156))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3169 =
             let uu____3170 = FStar_Syntax_Subst.compress t  in
             uu____3170.FStar_Syntax_Syntax.n  in
           (match uu____3169 with
            | FStar_Syntax_Syntax.Tm_type uu____3174 when
                let uu____3175 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3175 -> term_to_string t
            | uu____3177 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3180 = univ_to_string u  in
                     let uu____3182 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3180 uu____3182
                 | uu____3185 ->
                     let uu____3188 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3188))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3194 = FStar_Options.print_effect_args ()  in
             if uu____3194
             then
               let uu____3198 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3200 =
                 let uu____3202 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3202 (FStar_String.concat ", ")
                  in
               let uu____3217 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3219 =
                 let uu____3221 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3221 (FStar_String.concat ", ")
                  in
               let uu____3248 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3198
                 uu____3200 uu____3217 uu____3219 uu____3248
             else
               (let uu____3253 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3259  ->
                           match uu___9_3259 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3262 -> false)))
                    &&
                    (let uu____3265 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3265)
                   in
                if uu____3253
                then
                  let uu____3269 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3269
                else
                  (let uu____3274 =
                     ((let uu____3278 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3278) &&
                        (let uu____3281 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3281))
=======
           let uu____3148 =
             let uu____3149 = FStar_Syntax_Subst.compress t  in
             uu____3149.FStar_Syntax_Syntax.n  in
           (match uu____3148 with
            | FStar_Syntax_Syntax.Tm_type uu____3153 when
                let uu____3154 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3154 -> term_to_string t
            | uu____3156 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3159 = univ_to_string u  in
                     let uu____3161 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3159 uu____3161
                 | uu____3164 ->
                     let uu____3167 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3167))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3180 =
             let uu____3181 = FStar_Syntax_Subst.compress t  in
             uu____3181.FStar_Syntax_Syntax.n  in
           (match uu____3180 with
            | FStar_Syntax_Syntax.Tm_type uu____3185 when
                let uu____3186 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3186 -> term_to_string t
            | uu____3188 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3191 = univ_to_string u  in
                     let uu____3193 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3191 uu____3193
                 | uu____3196 ->
                     let uu____3199 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3199))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3205 = FStar_Options.print_effect_args ()  in
             if uu____3205
             then
               let uu____3209 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3211 =
                 let uu____3213 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3213 (FStar_String.concat ", ")
                  in
               let uu____3228 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3230 =
                 let uu____3232 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3232 (FStar_String.concat ", ")
                  in
               let uu____3259 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3209
                 uu____3211 uu____3228 uu____3230 uu____3259
             else
               (let uu____3264 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3270  ->
                           match uu___9_3270 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3273 -> false)))
                    &&
                    (let uu____3276 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3276)
                   in
                if uu____3264
                then
                  let uu____3280 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3280
                else
                  (let uu____3285 =
                     ((let uu____3289 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3289) &&
                        (let uu____3292 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3292))
>>>>>>> snap
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
<<<<<<< HEAD
                   if uu____3274
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3287 =
                        (let uu____3291 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3291) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3297  ->
                                   match uu___10_3297 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3300 -> false)))
                         in
                      if uu____3287
                      then
                        let uu____3304 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3304
                      else
                        (let uu____3309 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3311 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3309 uu____3311))))
              in
           let dec =
             let uu____3316 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3329  ->
                       match uu___11_3329 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3336 =
                             let uu____3338 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3338
                              in
                           [uu____3336]
                       | uu____3343 -> []))
                in
             FStar_All.pipe_right uu____3316 (FStar_String.concat " ")  in
=======
                   if uu____3285
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3298 =
                        (let uu____3302 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3302) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3308  ->
                                   match uu___10_3308 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3311 -> false)))
                         in
                      if uu____3298
                      then
                        let uu____3315 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3315
                      else
                        (let uu____3320 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3322 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3320 uu____3322))))
              in
           let dec =
             let uu____3327 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3340  ->
                       match uu___11_3340 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3347 =
                             let uu____3349 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3349
                              in
                           [uu____3347]
                       | uu____3354 -> []))
                in
             FStar_All.pipe_right uu____3327 (FStar_String.concat " ")  in
>>>>>>> snap
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
<<<<<<< HEAD
    | FStar_Syntax_Syntax.DECREASES uu____3362 -> ""
=======
    | FStar_Syntax_Syntax.DECREASES uu____3373 -> ""
>>>>>>> snap

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
<<<<<<< HEAD
  fun uu___12_3372  ->
    match uu___12_3372 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____3374,ps) ->
        let pats =
          let uu____3410 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3447 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3472  ->
                              match uu____3472 with
                              | (t,uu____3481) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3447
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3410 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3498 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3498
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3503) ->
        let uu____3508 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3508
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____3519 = sli m  in
        let uu____3521 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3519 uu____3521
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3531 = sli m  in
        let uu____3533 = sli m'  in
        let uu____3535 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3531
          uu____3533 uu____3535
=======
  fun uu___12_3383  ->
    match uu___12_3383 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____3385,ps) ->
        let pats =
          let uu____3421 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3458 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3483  ->
                              match uu____3483 with
                              | (t,uu____3492) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3458
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3421 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3509 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3509
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3514) ->
        let uu____3519 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3519
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____3530 = sli m  in
        let uu____3532 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3530 uu____3532
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3542 = sli m  in
        let uu____3544 = sli m'  in
        let uu____3546 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3542
          uu____3544 uu____3546
>>>>>>> snap

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
<<<<<<< HEAD
      let uu____3550 = FStar_Options.ugly ()  in
      if uu____3550
=======
      let uu____3561 = FStar_Options.ugly ()  in
      if uu____3561
>>>>>>> snap
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
<<<<<<< HEAD
      let uu____3571 = b  in
      match uu____3571 with
      | (a,imp) ->
          let n1 =
            let uu____3579 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3579
            then FStar_Util.JsonNull
            else
              (let uu____3584 =
                 let uu____3586 = nm_to_string a  in
                 imp_to_string uu____3586 imp  in
               FStar_Util.JsonStr uu____3584)
             in
          let t =
            let uu____3589 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3589  in
=======
      let uu____3582 = b  in
      match uu____3582 with
      | (a,imp) ->
          let n1 =
            let uu____3590 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3590
            then FStar_Util.JsonNull
            else
              (let uu____3595 =
                 let uu____3597 = nm_to_string a  in
                 imp_to_string uu____3597 imp  in
               FStar_Util.JsonStr uu____3595)
             in
          let t =
            let uu____3600 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3600  in
>>>>>>> snap
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
<<<<<<< HEAD
      let uu____3621 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3621
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3639 = FStar_Options.print_universes ()  in
    if uu____3639 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3655 =
      let uu____3657 = FStar_Options.ugly ()  in Prims.op_Negation uu____3657
       in
    if uu____3655
=======
      let uu____3632 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3632
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3650 = FStar_Options.print_universes ()  in
    if uu____3650 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3666 =
      let uu____3668 = FStar_Options.ugly ()  in Prims.op_Negation uu____3668
       in
    if uu____3666
>>>>>>> snap
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
<<<<<<< HEAD
      (let uu____3667 = s  in
       match uu____3667 with
       | (us,t) ->
           let uu____3679 =
             let uu____3681 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3681  in
           let uu____3685 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3679 uu____3685)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3695 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3697 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3700 =
      let uu____3702 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3702  in
    let uu____3706 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3708 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3695 uu____3697 uu____3700
      uu____3706 uu____3708
=======
      (let uu____3678 = s  in
       match uu____3678 with
       | (us,t) ->
           let uu____3690 =
             let uu____3692 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3692  in
           let uu____3696 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3690 uu____3696)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3706 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3708 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3711 =
      let uu____3713 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3713  in
    let uu____3717 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3719 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3706 uu____3708 uu____3711
      uu____3717 uu____3719
>>>>>>> snap
  
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
<<<<<<< HEAD
          let uu____3739 =
            let uu____3741 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3741  in
          if uu____3739
=======
          let uu____3750 =
            let uu____3752 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3752  in
          if uu____3750
>>>>>>> snap
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
<<<<<<< HEAD
               let uu____3762 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3762 (FStar_String.concat ",\n\t")
                in
             let eff_name =
               if
                 FStar_Pervasives_Native.fst
                   ed.FStar_Syntax_Syntax.is_layered
               then "layered_effect"
               else "new_effect"  in
             let match_wps_string =
               match ed.FStar_Syntax_Syntax.match_wps with
               | FStar_Util.Inl
                   { FStar_Syntax_Syntax.if_then_else = t1;
                     FStar_Syntax_Syntax.ite_wp = t2;
                     FStar_Syntax_Syntax.close_wp = t3;_}
                   ->
<<<<<<< HEAD
                   let uu____3791 = tscheme_to_string t1  in
                   let uu____3793 = tscheme_to_string t2  in
                   let uu____3795 = tscheme_to_string t3  in
                   FStar_Util.format3
                     "{\nif_then_else = %s;\nite_wp = %s\nclose_wp = %s\n}\n"
                     uu____3791 uu____3793 uu____3795
               | FStar_Util.Inr { FStar_Syntax_Syntax.conjunction = t;_} ->
                   let uu____3799 = tscheme_to_string t  in
                   FStar_Util.format1 "{\nconjunction = %s\n}\n" uu____3799
                in
             let uu____3802 =
               let uu____3806 =
                 let uu____3810 =
                   let uu____3814 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname  in
                   let uu____3816 =
                     let uu____3820 =
                       let uu____3822 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs
                          in
                       FStar_All.pipe_left enclose_universes uu____3822  in
                     let uu____3826 =
                       let uu____3830 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders
                          in
                       let uu____3833 =
                         let uu____3837 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature
                            in
                         let uu____3839 =
                           let uu____3843 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                              in
                           let uu____3845 =
                             let uu____3849 =
=======
               let uu____3773 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3773 (FStar_String.concat ",\n\t")
                in
             let uu____3788 =
               let uu____3792 =
                 let uu____3796 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____3798 =
                   let uu____3802 =
                     let uu____3804 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____3804  in
                   let uu____3808 =
                     let uu____3812 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____3815 =
                       let uu____3819 =
                         tscheme_to_string ed.FStar_Syntax_Syntax.signature
                          in
                       let uu____3821 =
                         let uu____3825 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____3827 =
                           let uu____3831 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____3833 =
                             let uu____3837 =
>>>>>>> snap
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.bind_wp
                                in
<<<<<<< HEAD
                             let uu____3851 =
                               let uu____3855 =
=======
                             let uu____3839 =
                               let uu____3843 =
>>>>>>> snap
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.stronger
                                  in
<<<<<<< HEAD
                               let uu____3857 =
                                 let uu____3861 =
                                   let uu____3865 =
=======
                   let uu____3787 = tscheme_to_string t1  in
                   let uu____3789 = tscheme_to_string t2  in
                   let uu____3791 = tscheme_to_string t3  in
                   FStar_Util.format3
                     "{\nif_then_else = %s;\nite_wp = %s\nclose_wp = %s\n}\n"
                     uu____3787 uu____3789 uu____3791
               | FStar_Util.Inr { FStar_Syntax_Syntax.conjunction = t;_} ->
                   let uu____3795 = tscheme_to_string t  in
                   FStar_Util.format1 "{\nconjunction = %s\n}\n" uu____3795
                in
             let uu____3798 =
               let uu____3802 =
                 let uu____3806 =
                   let uu____3810 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname  in
                   let uu____3812 =
                     let uu____3816 =
                       let uu____3818 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs
                          in
                       FStar_All.pipe_left enclose_universes uu____3818  in
                     let uu____3822 =
                       let uu____3826 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders
                          in
                       let uu____3829 =
                         let uu____3833 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature
                            in
                         let uu____3835 =
                           let uu____3839 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                              in
                           let uu____3841 =
                             let uu____3845 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.bind_wp
                                in
                             let uu____3847 =
                               let uu____3851 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.stronger
                                  in
                               let uu____3853 =
                                 let uu____3857 =
                                   let uu____3861 =
>>>>>>> snap
                                     match ed.FStar_Syntax_Syntax.trivial
                                     with
                                     | FStar_Pervasives_Native.None  -> ""
                                     | FStar_Pervasives_Native.Some t ->
                                         tscheme_to_string t
                                      in
<<<<<<< HEAD
                                   let uu____3870 =
                                     let uu____3874 =
=======
                               let uu____3845 =
                                 let uu____3849 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____3851 =
                                   let uu____3855 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____3857 =
                                     let uu____3861 =
>>>>>>> snap
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.repr
                                        in
<<<<<<< HEAD
                                     let uu____3876 =
                                       let uu____3880 =
=======
                                     let uu____3863 =
                                       let uu____3867 =
>>>>>>> snap
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.return_repr
                                          in
<<<<<<< HEAD
                                       let uu____3882 =
                                         let uu____3886 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.bind_repr
                                            in
                                         let uu____3888 =
                                           let uu____3892 =
=======
                                   let uu____3866 =
                                     let uu____3870 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.repr
                                        in
                                     let uu____3872 =
                                       let uu____3876 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.return_repr
                                          in
                                       let uu____3878 =
                                         let uu____3882 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.bind_repr
                                            in
                                         let uu____3884 =
                                           let uu____3888 =
>>>>>>> snap
                                             match ed.FStar_Syntax_Syntax.stronger_repr
                                             with
                                             | FStar_Pervasives_Native.None 
                                                 -> ""
                                             | FStar_Pervasives_Native.Some t
                                                 -> tscheme_to_string t
                                              in
<<<<<<< HEAD
                                           let uu____3897 =
                                             let uu____3901 =
                                               actions_to_string
                                                 ed.FStar_Syntax_Syntax.actions
                                                in
                                             [uu____3901]  in
                                           uu____3892 :: uu____3897  in
                                         uu____3886 :: uu____3888  in
                                       uu____3880 :: uu____3882  in
                                     uu____3874 :: uu____3876  in
                                   uu____3865 :: uu____3870  in
                                 match_wps_string :: uu____3861  in
                               uu____3855 :: uu____3857  in
                             uu____3849 :: uu____3851  in
                           uu____3843 :: uu____3845  in
                         uu____3837 :: uu____3839  in
                       uu____3830 :: uu____3833  in
                     uu____3820 :: uu____3826  in
                   uu____3814 :: uu____3816  in
                 (if for_free then "_for_free " else "") :: uu____3810  in
               eff_name :: uu____3806  in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  return_wp     = %s\n; bind_wp       = %s\n; stronger      = %s\n; match_wps     = %s\n; trivial       = %s\n; repr          = %s\n; return_repr   = %s\n; bind_repr     = %s\n; stronger_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____3802)
=======
                                       let uu____3869 =
                                         let uu____3873 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.bind_repr
                                            in
                                         let uu____3875 =
                                           let uu____3879 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.return_repr
                                              in
                                           let uu____3881 =
                                             let uu____3885 =
                                               actions_to_string
                                                 ed.FStar_Syntax_Syntax.actions
                                                in
                                             [uu____3885]  in
                                           uu____3879 :: uu____3881  in
                                         uu____3873 :: uu____3875  in
                                       uu____3867 :: uu____3869  in
                                     uu____3861 :: uu____3863  in
                                   uu____3855 :: uu____3857  in
                                 uu____3849 :: uu____3851  in
                               uu____3843 :: uu____3845  in
                             uu____3837 :: uu____3839  in
                           uu____3831 :: uu____3833  in
                         uu____3825 :: uu____3827  in
                       uu____3819 :: uu____3821  in
                     uu____3812 :: uu____3815  in
                   uu____3802 :: uu____3808  in
                 uu____3796 :: uu____3798  in
               (if for_free then "_for_free " else "") :: uu____3792  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____3788)
>>>>>>> snap
=======
                                           let uu____3893 =
                                             let uu____3897 =
                                               actions_to_string
                                                 ed.FStar_Syntax_Syntax.actions
                                                in
                                             [uu____3897]  in
                                           uu____3888 :: uu____3893  in
                                         uu____3882 :: uu____3884  in
                                       uu____3876 :: uu____3878  in
                                     uu____3870 :: uu____3872  in
                                   uu____3861 :: uu____3866  in
                                 match_wps_string :: uu____3857  in
                               uu____3851 :: uu____3853  in
                             uu____3845 :: uu____3847  in
                           uu____3839 :: uu____3841  in
                         uu____3833 :: uu____3835  in
                       uu____3826 :: uu____3829  in
                     uu____3816 :: uu____3822  in
                   uu____3810 :: uu____3812  in
                 (if for_free then "_for_free " else "") :: uu____3806  in
               eff_name :: uu____3802  in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  return_wp     = %s\n; bind_wp       = %s\n; stronger      = %s\n; match_wps     = %s\n; trivial       = %s\n; repr          = %s\n; return_repr   = %s\n; bind_repr     = %s\n; stronger_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____3798)
>>>>>>> snap
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se  ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
<<<<<<< HEAD
        let uu____3961 = FStar_All.pipe_right ts_opt FStar_Util.must  in
        FStar_All.pipe_right uu____3961 tscheme_to_string
      else "<None>"  in
    let uu____3968 = lid_to_string se.FStar_Syntax_Syntax.source  in
    let uu____3970 = lid_to_string se.FStar_Syntax_Syntax.target  in
    let uu____3972 = tsopt_to_string se.FStar_Syntax_Syntax.lift  in
    let uu____3974 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp  in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____3968 uu____3970 uu____3972 uu____3974
=======
        let uu____3957 = FStar_All.pipe_right ts_opt FStar_Util.must  in
        FStar_All.pipe_right uu____3957 tscheme_to_string
      else "<None>"  in
    let uu____3964 = lid_to_string se.FStar_Syntax_Syntax.source  in
    let uu____3966 = lid_to_string se.FStar_Syntax_Syntax.target  in
    let uu____3968 = tsopt_to_string se.FStar_Syntax_Syntax.lift  in
    let uu____3970 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp  in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____3964 uu____3966 uu____3968 uu____3970
>>>>>>> snap
  
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
<<<<<<< HEAD
<<<<<<< HEAD
          (lid,univs1,tps,k,uu____4009,uu____4010) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4026 = FStar_Options.print_universes ()  in
          if uu____4026
          then
            let uu____4030 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____4030 binders_str term_str
=======
          (lid,univs1,tps,k,uu____3957,uu____3958) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____3974 = FStar_Options.print_universes ()  in
          if uu____3974
          then
            let uu____3978 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____3978 binders_str term_str
>>>>>>> snap
=======
          (lid,univs1,tps,k,uu____4005,uu____4006) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4022 = FStar_Options.print_universes ()  in
          if uu____4022
          then
            let uu____4026 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____4026 binders_str term_str
>>>>>>> snap
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
<<<<<<< HEAD
<<<<<<< HEAD
          (lid,univs1,t,uu____4039,uu____4040,uu____4041) ->
          let uu____4048 = FStar_Options.print_universes ()  in
          if uu____4048
          then
            let uu____4052 = univ_names_to_string univs1  in
            let uu____4054 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4052
              lid.FStar_Ident.str uu____4054
          else
            (let uu____4059 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____4059)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____4065 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4067 =
            let uu____4069 = FStar_Options.print_universes ()  in
            if uu____4069
            then
              let uu____4073 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____4073
            else ""  in
          let uu____4079 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4065
            lid.FStar_Ident.str uu____4067 uu____4079
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4085 = FStar_Options.print_universes ()  in
          if uu____4085
          then
            let uu____4089 = univ_names_to_string us  in
            let uu____4091 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____4089 uu____4091
          else
            (let uu____4096 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4096)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4100) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4106 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____4106
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4110) ->
          let uu____4119 =
            let uu____4121 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4121 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____4119
=======
          (lid,univs1,t,uu____3987,uu____3988,uu____3989) ->
          let uu____3996 = FStar_Options.print_universes ()  in
          if uu____3996
          then
            let uu____4000 = univ_names_to_string univs1  in
            let uu____4002 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4000
              lid.FStar_Ident.str uu____4002
          else
            (let uu____4007 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____4007)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____4013 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4015 =
            let uu____4017 = FStar_Options.print_universes ()  in
            if uu____4017
            then
              let uu____4021 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____4021
            else ""  in
          let uu____4027 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4013
            lid.FStar_Ident.str uu____4015 uu____4027
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4033 = FStar_Options.print_universes ()  in
          if uu____4033
          then
            let uu____4037 = univ_names_to_string us  in
            let uu____4039 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____4037 uu____4039
          else
            (let uu____4044 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4044)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4048) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4054 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____4054
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4058) ->
          let uu____4067 =
            let uu____4069 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4069 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____4067
>>>>>>> snap
=======
          (lid,univs1,t,uu____4035,uu____4036,uu____4037) ->
          let uu____4044 = FStar_Options.print_universes ()  in
          if uu____4044
          then
            let uu____4048 = univ_names_to_string univs1  in
            let uu____4050 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4048
              lid.FStar_Ident.str uu____4050
          else
            (let uu____4055 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____4055)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____4061 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4063 =
            let uu____4065 = FStar_Options.print_universes ()  in
            if uu____4065
            then
              let uu____4069 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____4069
            else ""  in
          let uu____4075 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4061
            lid.FStar_Ident.str uu____4063 uu____4075
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4081 = FStar_Options.print_universes ()  in
          if uu____4081
          then
            let uu____4085 = univ_names_to_string us  in
            let uu____4087 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____4085 uu____4087
          else
            (let uu____4092 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4092)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4096) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4102 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____4102
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4106) ->
          let uu____4115 =
            let uu____4117 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4117 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____4115
>>>>>>> snap
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          eff_decl_to_string' false x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
          eff_decl_to_string' true x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
<<<<<<< HEAD
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
<<<<<<< HEAD
          let uu____4146 = FStar_Options.print_universes ()  in
          if uu____4146
          then
            let uu____4150 =
              let uu____4155 =
=======
      | FStar_Syntax_Syntax.Sig_sub_effect se ->
          let lift_wp =
            match ((se.FStar_Syntax_Syntax.lift_wp),
                    (se.FStar_Syntax_Syntax.lift))
            with
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                -> failwith "impossible"
            | (FStar_Pervasives_Native.Some lift_wp,uu____4114) -> lift_wp
            | (uu____4121,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____4129 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____4129 with
           | (us,t) ->
               let uu____4141 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____4143 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____4145 = univ_names_to_string us  in
               let uu____4147 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____4141
                 uu____4143 uu____4145 uu____4147)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____4159 = FStar_Options.print_universes ()  in
          if uu____4159
          then
            let uu____4163 =
              let uu____4168 =
>>>>>>> snap
=======
          let uu____4142 = FStar_Options.print_universes ()  in
          if uu____4142
          then
            let uu____4146 =
              let uu____4151 =
>>>>>>> snap
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
<<<<<<< HEAD
<<<<<<< HEAD
              FStar_Syntax_Subst.open_univ_vars univs1 uu____4155  in
            (match uu____4150 with
             | (univs2,t) ->
                 let uu____4169 =
                   let uu____4174 =
                     let uu____4175 = FStar_Syntax_Subst.compress t  in
                     uu____4175.FStar_Syntax_Syntax.n  in
                   match uu____4174 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4204 -> failwith "impossible"  in
                 (match uu____4169 with
                  | (tps1,c1) ->
                      let uu____4213 = sli l  in
                      let uu____4215 = univ_names_to_string univs2  in
                      let uu____4217 = binders_to_string " " tps1  in
                      let uu____4220 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4213
                        uu____4215 uu____4217 uu____4220))
          else
            (let uu____4225 = sli l  in
             let uu____4227 = binders_to_string " " tps  in
             let uu____4230 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4225 uu____4227
               uu____4230)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4239 =
            let uu____4241 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4241  in
          let uu____4251 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4239 uu____4251
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4257 ->
        let uu____4260 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____4260 (Prims.op_Hat "\n" basic)
=======
              FStar_Syntax_Subst.open_univ_vars univs1 uu____4168  in
            (match uu____4163 with
             | (univs2,t) ->
                 let uu____4182 =
                   let uu____4187 =
                     let uu____4188 = FStar_Syntax_Subst.compress t  in
                     uu____4188.FStar_Syntax_Syntax.n  in
                   match uu____4187 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4217 -> failwith "impossible"  in
                 (match uu____4182 with
                  | (tps1,c1) ->
                      let uu____4226 = sli l  in
                      let uu____4228 = univ_names_to_string univs2  in
                      let uu____4230 = binders_to_string " " tps1  in
                      let uu____4233 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4226
                        uu____4228 uu____4230 uu____4233))
          else
            (let uu____4238 = sli l  in
             let uu____4240 = binders_to_string " " tps  in
             let uu____4243 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4238 uu____4240
               uu____4243)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4252 =
            let uu____4254 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4254  in
          let uu____4264 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4252 uu____4264
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4270 ->
        let uu____4273 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____4273 (Prims.op_Hat "\n" basic)
>>>>>>> snap
=======
              FStar_Syntax_Subst.open_univ_vars univs1 uu____4151  in
            (match uu____4146 with
             | (univs2,t) ->
                 let uu____4165 =
                   let uu____4170 =
                     let uu____4171 = FStar_Syntax_Subst.compress t  in
                     uu____4171.FStar_Syntax_Syntax.n  in
                   match uu____4170 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4200 -> failwith "impossible"  in
                 (match uu____4165 with
                  | (tps1,c1) ->
                      let uu____4209 = sli l  in
                      let uu____4211 = univ_names_to_string univs2  in
                      let uu____4213 = binders_to_string " " tps1  in
                      let uu____4216 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4209
                        uu____4211 uu____4213 uu____4216))
          else
            (let uu____4221 = sli l  in
             let uu____4223 = binders_to_string " " tps  in
             let uu____4226 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4221 uu____4223
               uu____4226)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4235 =
            let uu____4237 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4237  in
          let uu____4247 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4235 uu____4247
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4253 ->
        let uu____4256 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____4256 (Prims.op_Hat "\n" basic)
>>>>>>> snap
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____4277 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4277 msg
=======
      let uu____4290 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4290 msg
>>>>>>> snap
=======
      let uu____4273 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4273 msg
>>>>>>> snap
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
<<<<<<< HEAD
<<<<<<< HEAD
        ((uu____4288,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4290;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4292;
                       FStar_Syntax_Syntax.lbdef = uu____4293;
                       FStar_Syntax_Syntax.lbattrs = uu____4294;
                       FStar_Syntax_Syntax.lbpos = uu____4295;_}::[]),uu____4296)
        ->
        let uu____4319 = lbname_to_string lb  in
        let uu____4321 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4319 uu____4321
    | uu____4324 ->
        let uu____4325 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____4325 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4349 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4351 =
      let uu____4353 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4353 (FStar_String.concat "\n")  in
    let uu____4363 =
      let uu____4365 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4365 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4349
      uu____4351 uu____4363
=======
        ((uu____4301,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4303;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4305;
                       FStar_Syntax_Syntax.lbdef = uu____4306;
                       FStar_Syntax_Syntax.lbattrs = uu____4307;
                       FStar_Syntax_Syntax.lbpos = uu____4308;_}::[]),uu____4309)
        ->
        let uu____4332 = lbname_to_string lb  in
        let uu____4334 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4332 uu____4334
    | uu____4337 ->
        let uu____4338 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____4338 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4362 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4364 =
      let uu____4366 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4366 (FStar_String.concat "\n")  in
    let uu____4376 =
      let uu____4378 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4378 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4362
      uu____4364 uu____4376
  
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
          (let uu____4422 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____4422))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____4431 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____4431)));
    FStar_Util.string_of_string_builder strb
>>>>>>> snap
=======
        ((uu____4284,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4286;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4288;
                       FStar_Syntax_Syntax.lbdef = uu____4289;
                       FStar_Syntax_Syntax.lbattrs = uu____4290;
                       FStar_Syntax_Syntax.lbpos = uu____4291;_}::[]),uu____4292)
        ->
        let uu____4315 = lbname_to_string lb  in
        let uu____4317 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4315 uu____4317
    | uu____4320 ->
        let uu____4321 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____4321 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4345 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4347 =
      let uu____4349 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4349 (FStar_String.concat "\n")  in
    let uu____4359 =
      let uu____4361 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4361 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4345
      uu____4347 uu____4359
>>>>>>> snap
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
<<<<<<< HEAD
<<<<<<< HEAD
           (let uu____4415 = f x  in
            FStar_Util.string_builder_append strb uu____4415);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4424 = f x1  in
                 FStar_Util.string_builder_append strb uu____4424)) xs;
=======
           (let uu____4472 = f x  in
            FStar_Util.string_builder_append strb uu____4472);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4481 = f x1  in
                 FStar_Util.string_builder_append strb uu____4481)) xs;
>>>>>>> snap
=======
           (let uu____4411 = f x  in
            FStar_Util.string_builder_append strb uu____4411);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4420 = f x1  in
                 FStar_Util.string_builder_append strb uu____4420)) xs;
>>>>>>> snap
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
<<<<<<< HEAD
<<<<<<< HEAD
           (let uu____4471 = f x  in
            FStar_Util.string_builder_append strb uu____4471);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4480 = f x1  in
                 FStar_Util.string_builder_append strb uu____4480)) xs;
=======
           (let uu____4528 = f x  in
            FStar_Util.string_builder_append strb uu____4528);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4537 = f x1  in
                 FStar_Util.string_builder_append strb uu____4537)) xs;
>>>>>>> snap
=======
           (let uu____4467 = f x  in
            FStar_Util.string_builder_append strb uu____4467);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4476 = f x1  in
                 FStar_Util.string_builder_append strb uu____4476)) xs;
>>>>>>> snap
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
<<<<<<< HEAD
<<<<<<< HEAD
      let uu____4502 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4502
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___13_4515  ->
    match uu___13_4515 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4531 =
          let uu____4533 =
            let uu____4535 =
              let uu____4537 =
                let uu____4539 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4539 (FStar_String.concat " ")  in
              Prims.op_Hat uu____4537 ")"  in
            Prims.op_Hat " " uu____4535  in
          Prims.op_Hat h uu____4533  in
        Prims.op_Hat "(" uu____4531
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4554 =
          let uu____4556 = emb_typ_to_string a  in
          let uu____4558 =
            let uu____4560 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____4560  in
          Prims.op_Hat uu____4556 uu____4558  in
        Prims.op_Hat "(" uu____4554
=======
      let uu____4559 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4559
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___13_4572  ->
    match uu___13_4572 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4588 =
          let uu____4590 =
            let uu____4592 =
              let uu____4594 =
                let uu____4596 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4596 (FStar_String.concat " ")  in
              Prims.op_Hat uu____4594 ")"  in
            Prims.op_Hat " " uu____4592  in
          Prims.op_Hat h uu____4590  in
        Prims.op_Hat "(" uu____4588
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4611 =
          let uu____4613 = emb_typ_to_string a  in
          let uu____4615 =
            let uu____4617 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____4617  in
          Prims.op_Hat uu____4613 uu____4615  in
        Prims.op_Hat "(" uu____4611
>>>>>>> snap
=======
      let uu____4498 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4498
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___13_4511  ->
    match uu___13_4511 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4527 =
          let uu____4529 =
            let uu____4531 =
              let uu____4533 =
                let uu____4535 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4535 (FStar_String.concat " ")  in
              Prims.op_Hat uu____4533 ")"  in
            Prims.op_Hat " " uu____4531  in
          Prims.op_Hat h uu____4529  in
        Prims.op_Hat "(" uu____4527
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4550 =
          let uu____4552 = emb_typ_to_string a  in
          let uu____4554 =
            let uu____4556 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____4556  in
          Prims.op_Hat uu____4552 uu____4554  in
        Prims.op_Hat "(" uu____4550
>>>>>>> snap
  