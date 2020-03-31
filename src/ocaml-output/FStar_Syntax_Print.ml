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
               (FStar_Syntax_Syntax.Meta
               (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t))) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____519,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____520)) -> false
            | (uu____525,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____526)) -> false
            | uu____530 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____548 =
      let uu____549 = FStar_Syntax_Subst.compress e  in
      uu____549.FStar_Syntax_Syntax.n  in
    match uu____548 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____610 =
          (is_lex_cons f) && ((FStar_List.length exps) = (Prims.of_int (2)))
           in
        if uu____610
        then
          let uu____619 =
            let uu____624 = FStar_List.nth exps Prims.int_one  in
            reconstruct_lex uu____624  in
          (match uu____619 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____635 =
                 let uu____638 = FStar_List.nth exps Prims.int_zero  in
                 uu____638 :: xs  in
               FStar_Pervasives_Native.Some uu____635
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____650 ->
        let uu____651 = is_lex_top e  in
        if uu____651
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____699 = f hd1  in if uu____699 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____731 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____731
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____762 = get_lid e  in find_lid uu____762 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____774 = get_lid e  in find_lid uu____774 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____786 = get_lid t  in find_lid uu____786 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___3_800  ->
    match uu___3_800 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____811 = FStar_Options.hide_uvar_nums ()  in
    if uu____811
    then "?"
    else
      (let uu____818 =
         let uu____820 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____820 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____818)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____832 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____834 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____832 uu____834
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____860 = FStar_Options.hide_uvar_nums ()  in
    if uu____860
    then "?"
    else
      (let uu____867 =
         let uu____869 =
           let uu____871 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____871 FStar_Util.string_of_int  in
         let uu____875 =
           let uu____877 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.op_Hat ":" uu____877  in
         Prims.op_Hat uu____869 uu____875  in
       Prims.op_Hat "?" uu____867)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____905 = FStar_Syntax_Subst.compress_univ u  in
      match uu____905 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 -> int_of_univ (n1 + Prims.int_one) u1
      | uu____918 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____929 = FStar_Syntax_Subst.compress_univ u  in
    match uu____929 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____940 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____940
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____947 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____947
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____952 = int_of_univ Prims.int_one u1  in
        (match uu____952 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____973 = univ_to_string u2  in
             let uu____975 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____973 uu____975)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____981 =
          let uu____983 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____983 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____981
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____1002 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____1002 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____1019 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____1019 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___4_1037  ->
    match uu___4_1037 with
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
        let uu____1053 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____1053
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1058 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____1058
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1071 =
          let uu____1073 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1073  in
        let uu____1074 =
          let uu____1076 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1076 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____1071 uu____1074
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1102 =
          let uu____1104 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1104  in
        let uu____1105 =
          let uu____1107 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1107 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1102 uu____1105
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1124 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____1124
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
    | uu____1147 ->
        let uu____1150 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____1150 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1178 ->
        let uu____1181 = quals_to_string quals  in
        Prims.op_Hat uu____1181 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1363 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____1363
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1367 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____1367
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1371 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____1371
    | FStar_Syntax_Syntax.Tm_uinst uu____1374 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1382 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1384 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1386,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1387;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1401,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1402;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1416 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1436 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1452 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1460 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1478 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1502 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1530 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1545 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed uu____1559 -> "Tm_delayed-resolved"
    | FStar_Syntax_Syntax.Tm_meta (uu____1575,m) ->
        let uu____1581 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____1581
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1585 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1588 =
      let uu____1590 = FStar_Options.ugly ()  in Prims.op_Negation uu____1590
       in
    if uu____1588
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1604 = FStar_Options.print_implicits ()  in
         if uu____1604 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1612 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1629,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1655,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____1657;
             FStar_Syntax_Syntax.rng = uu____1658;_}
           ->
           let uu____1669 =
             let uu____1671 =
               let uu____1673 = FStar_Thunk.force thunk1  in
               term_to_string uu____1673  in
             Prims.op_Hat uu____1671 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____1669
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1679 =
             let uu____1681 =
               let uu____1683 =
                 let uu____1684 =
                   let uu____1693 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1693  in
                 uu____1684 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1683  in
             Prims.op_Hat uu____1681 "]"  in
           Prims.op_Hat "[lazy:" uu____1679
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1762 =
                  match uu____1762 with
                  | (bv,t) ->
                      let uu____1770 = bv_to_string bv  in
                      let uu____1772 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1770 uu____1772
                   in
                let uu____1775 = term_to_string tm  in
                let uu____1777 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1775 uu____1777
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1786 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1786)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_pattern (uu____1790,ps)) ->
           let pats =
             let uu____1830 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1867 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1892  ->
                                 match uu____1892 with
                                 | (t1,uu____1901) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1867
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1830 (FStar_String.concat "\\/")  in
           let uu____1916 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1916
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1930 = tag_of_term t  in
           let uu____1932 = sli m  in
           let uu____1934 = term_to_string t'  in
           let uu____1936 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1930 uu____1932
             uu____1934 uu____1936
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1951 = tag_of_term t  in
           let uu____1953 = term_to_string t'  in
           let uu____1955 = sli m0  in
           let uu____1957 = sli m1  in
           let uu____1959 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1951
             uu____1953 uu____1955 uu____1957 uu____1959
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1974 = FStar_Range.string_of_range r  in
           let uu____1976 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1974
             uu____1976
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1985 = lid_to_string l  in
           let uu____1987 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1989 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1985 uu____1987
             uu____1989
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1993) ->
           let uu____1998 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1998
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2002 = db_to_string x3  in
           let uu____2004 =
             let uu____2006 =
               let uu____2008 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____2008 ")"  in
             Prims.op_Hat ":(" uu____2006  in
           Prims.op_Hat uu____2002 uu____2004
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2015)) ->
           let uu____2030 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2030
           then ctx_uvar_to_string u
           else
             (let uu____2036 =
                let uu____2038 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2038  in
              Prims.op_Hat "?" uu____2036)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2061 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2061
           then
             let uu____2065 = ctx_uvar_to_string u  in
             let uu____2067 =
               let uu____2069 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2069 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2065 uu____2067
           else
             (let uu____2088 =
                let uu____2090 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2090  in
              Prims.op_Hat "?" uu____2088)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2097 = FStar_Options.print_universes ()  in
           if uu____2097
           then
             let uu____2101 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2101
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2129 = binders_to_string " -> " bs  in
           let uu____2132 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2129 uu____2132
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2164 = binders_to_string " " bs  in
                let uu____2167 = term_to_string t2  in
                let uu____2169 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2178 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2178)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2164 uu____2167
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____2169
            | uu____2182 ->
                let uu____2185 = binders_to_string " " bs  in
                let uu____2188 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2185 uu____2188)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2197 = bv_to_string xt  in
           let uu____2199 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2202 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2197 uu____2199 uu____2202
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2234 = term_to_string t  in
           let uu____2236 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2234 uu____2236
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2259 = lbs_to_string [] lbs  in
           let uu____2261 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2259 uu____2261
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2326 =
                   let uu____2328 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____2328
                     (FStar_Util.dflt "default")
                    in
                 let uu____2339 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2326 uu____2339
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2360 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2360
              in
           let uu____2363 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2363 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____2404 = term_to_string head1  in
           let uu____2406 =
             let uu____2408 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string)
                in
             FStar_Util.concat_l "\n\t|" uu____2408  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2404 uu____2406
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2426 = FStar_Options.print_universes ()  in
           if uu____2426
           then
             let uu____2430 = term_to_string t  in
             let uu____2432 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2430 uu____2432
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____2438  ->
    match uu____2438 with
    | (p,wopt,e) ->
        let uu____2460 = FStar_All.pipe_right p pat_to_string  in
        let uu____2463 =
          match wopt with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____2474 = FStar_All.pipe_right w term_to_string  in
              FStar_Util.format1 "when %s" uu____2474
           in
        let uu____2478 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format3 "%s %s -> %s" uu____2460 uu____2463 uu____2478

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2483 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2486 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2488 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2483 uu____2486
      uu____2488

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2491  ->
    match uu___5_2491 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2497 = FStar_Util.string_of_int i  in
        let uu____2499 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2497 uu____2499
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2506 = bv_to_string x  in
        let uu____2508 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2506 uu____2508
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2517 = bv_to_string x  in
        let uu____2519 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2517 uu____2519
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2526 = FStar_Util.string_of_int i  in
        let uu____2528 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2526 uu____2528
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2535 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2535

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2539 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2539 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2555 =
      let uu____2557 = FStar_Options.ugly ()  in Prims.op_Negation uu____2557
       in
    if uu____2555
    then
      let e =
        let uu____2562 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2562  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2591 = fv_to_string l  in
           let uu____2593 =
             let uu____2595 =
               FStar_List.map
                 (fun uu____2609  ->
                    match uu____2609 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2595 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2591 uu____2593
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2634) ->
           let uu____2639 = FStar_Options.print_bound_var_types ()  in
           if uu____2639
           then
             let uu____2643 = bv_to_string x1  in
             let uu____2645 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2643 uu____2645
           else
             (let uu____2650 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2650)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2654 = FStar_Options.print_bound_var_types ()  in
           if uu____2654
           then
             let uu____2658 = bv_to_string x1  in
             let uu____2660 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2658 uu____2660
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2667 = FStar_Options.print_bound_var_types ()  in
           if uu____2667
           then
             let uu____2671 = bv_to_string x1  in
             let uu____2673 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2671 uu____2673
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2682 = quals_to_string' quals  in
      let uu____2684 =
        let uu____2686 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2706 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2708 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2710 =
                    let uu____2712 = FStar_Options.print_universes ()  in
                    if uu____2712
                    then
                      let uu____2716 =
                        let uu____2718 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____2718 ">"  in
                      Prims.op_Hat "<" uu____2716
                    else ""  in
                  let uu____2725 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2727 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2706
                    uu____2708 uu____2710 uu____2725 uu____2727))
           in
        FStar_Util.concat_l "\n and " uu____2686  in
      FStar_Util.format3 "%slet %s %s" uu____2682
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2684

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2742  ->
    match uu___6_2742 with
    | [] -> ""
    | tms ->
        let uu____2750 =
          let uu____2752 =
            FStar_List.map
              (fun t  ->
                 let uu____2760 = term_to_string t  in paren uu____2760) tms
             in
          FStar_All.pipe_right uu____2752 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2750

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___7_2769  ->
      match uu___7_2769 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.op_Hat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.op_Hat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.op_Hat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.op_Hat "[|" (Prims.op_Hat s "|]")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
          let uu____2787 =
            let uu____2789 = term_to_string t  in
            Prims.op_Hat uu____2789 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____2787
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
          (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
          let uu____2796 =
            let uu____2798 = term_to_string t  in
            Prims.op_Hat uu____2798 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[@" uu____2796
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
      let uu____2816 =
        let uu____2818 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2818  in
      if uu____2816
      then
        let uu____2822 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2822 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
        (let uu____2833 = b  in
         match uu____2833 with
         | (a,imp) ->
             let uu____2847 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2847
             then
               let uu____2851 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat "_:" uu____2851
             else
               (let uu____2856 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2859 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2859)
                   in
                if uu____2856
                then
                  let uu____2863 = nm_to_string a  in
                  imp_to_string uu____2863 imp
                else
                  (let uu____2867 =
                     let uu____2869 = nm_to_string a  in
                     let uu____2871 =
                       let uu____2873 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____2873  in
                     Prims.op_Hat uu____2869 uu____2871  in
                   imp_to_string uu____2867 imp)))

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
        let uu____2892 = FStar_Options.print_implicits ()  in
        if uu____2892 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2903 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2903 (FStar_String.concat sep)
      else
        (let uu____2931 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2931 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_2945  ->
    match uu___8_2945 with
    | (a,imp) ->
        let uu____2959 = term_to_string a  in imp_to_string uu____2959 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2971 = FStar_Options.print_implicits ()  in
      if uu____2971 then args else filter_imp args  in
    let uu____2986 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2986 (FStar_String.concat " ")

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____3014 =
      let uu____3016 = FStar_Options.ugly ()  in Prims.op_Negation uu____3016
       in
    if uu____3014
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____3037 =
             let uu____3038 = FStar_Syntax_Subst.compress t  in
             uu____3038.FStar_Syntax_Syntax.n  in
           (match uu____3037 with
            | FStar_Syntax_Syntax.Tm_type uu____3042 when
                let uu____3043 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3043 -> term_to_string t
            | uu____3045 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3048 = univ_to_string u  in
                     let uu____3050 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3048 uu____3050
                 | uu____3053 ->
                     let uu____3056 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3056))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3069 =
             let uu____3070 = FStar_Syntax_Subst.compress t  in
             uu____3070.FStar_Syntax_Syntax.n  in
           (match uu____3069 with
            | FStar_Syntax_Syntax.Tm_type uu____3074 when
                let uu____3075 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3075 -> term_to_string t
            | uu____3077 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3080 = univ_to_string u  in
                     let uu____3082 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3080 uu____3082
                 | uu____3085 ->
                     let uu____3088 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3088))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3094 = FStar_Options.print_effect_args ()  in
             if uu____3094
             then
               let uu____3098 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3100 =
                 let uu____3102 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3102 (FStar_String.concat ", ")
                  in
               let uu____3117 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3119 =
                 let uu____3121 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3121 (FStar_String.concat ", ")
                  in
               let uu____3148 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3098
                 uu____3100 uu____3117 uu____3119 uu____3148
             else
               (let uu____3153 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3159  ->
                           match uu___9_3159 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3162 -> false)))
                    &&
                    (let uu____3165 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3165)
                   in
                if uu____3153
                then
                  let uu____3169 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3169
                else
                  (let uu____3174 =
                     ((let uu____3178 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3178) &&
                        (let uu____3181 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3181))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____3174
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3187 =
                        (let uu____3191 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3191) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3197  ->
                                   match uu___10_3197 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3200 -> false)))
                         in
                      if uu____3187
                      then
                        let uu____3204 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3204
                      else
                        (let uu____3209 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3211 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3209 uu____3211))))
              in
           let dec =
             let uu____3216 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3229  ->
                       match uu___11_3229 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3236 =
                             let uu____3238 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3238
                              in
                           [uu____3236]
                       | uu____3243 -> []))
                in
             FStar_All.pipe_right uu____3216 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____3262 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_3272  ->
    match uu___12_3272 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____3274,ps) ->
        let pats =
          let uu____3310 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3347 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3372  ->
                              match uu____3372 with
                              | (t,uu____3381) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3347
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3310 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3398 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3398
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3403) ->
        let uu____3408 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3408
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____3419 = sli m  in
        let uu____3421 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3419 uu____3421
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3431 = sli m  in
        let uu____3433 = sli m'  in
        let uu____3435 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3431
          uu____3433 uu____3435

let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq  -> aqual_to_string' "" aq 
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____3458 = FStar_Options.ugly ()  in
      if uu____3458
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
      let uu____3480 = FStar_Options.ugly ()  in
      if uu____3480
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
      let uu____3501 = b  in
      match uu____3501 with
      | (a,imp) ->
          let n1 =
            let uu____3509 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3509
            then FStar_Util.JsonNull
            else
              (let uu____3514 =
                 let uu____3516 = nm_to_string a  in
                 imp_to_string uu____3516 imp  in
               FStar_Util.JsonStr uu____3514)
             in
          let t =
            let uu____3519 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3519  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____3551 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3551
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3569 = FStar_Options.print_universes ()  in
    if uu____3569 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3585 =
      let uu____3587 = FStar_Options.ugly ()  in Prims.op_Negation uu____3587
       in
    if uu____3585
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
      (let uu____3597 = s  in
       match uu____3597 with
       | (us,t) ->
           let uu____3609 =
             let uu____3611 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3611  in
           let uu____3615 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3609 uu____3615)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3625 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3627 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3630 =
      let uu____3632 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3632  in
    let uu____3636 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3638 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3625 uu____3627 uu____3630
      uu____3636 uu____3638
  
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs  ->
    let tscheme_opt_to_string uu___13_3656 =
      match uu___13_3656 with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None  -> "None"  in
    let uu____3662 =
      let uu____3666 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____3668 =
        let uu____3672 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp
           in
        let uu____3674 =
          let uu____3678 =
            tscheme_to_string combs.FStar_Syntax_Syntax.stronger  in
          let uu____3680 =
            let uu____3684 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else  in
            let uu____3686 =
              let uu____3690 =
                tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp  in
              let uu____3692 =
                let uu____3696 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp  in
                let uu____3698 =
                  let uu____3702 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial  in
                  let uu____3704 =
                    let uu____3708 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr
                       in
                    let uu____3710 =
                      let uu____3714 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr
                         in
                      let uu____3716 =
                        let uu____3720 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr
                           in
                        [uu____3720]  in
                      uu____3714 :: uu____3716  in
                    uu____3708 :: uu____3710  in
                  uu____3702 :: uu____3704  in
                uu____3696 :: uu____3698  in
              uu____3690 :: uu____3692  in
            uu____3684 :: uu____3686  in
          uu____3678 :: uu____3680  in
        uu____3672 :: uu____3674  in
      uu____3666 :: uu____3668  in
    FStar_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu____3662
  
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs  ->
    let to_str uu____3751 =
      match uu____3751 with
      | (ts_t,ts_ty) ->
          let uu____3759 = tscheme_to_string ts_t  in
          let uu____3761 = tscheme_to_string ts_ty  in
          FStar_Util.format2 "(%s) : (%s)" uu____3759 uu____3761
       in
    let uu____3764 =
      let uu____3768 =
        FStar_Ident.string_of_lid combs.FStar_Syntax_Syntax.l_base_effect  in
      let uu____3770 =
        let uu____3774 = to_str combs.FStar_Syntax_Syntax.l_repr  in
        let uu____3776 =
          let uu____3780 = to_str combs.FStar_Syntax_Syntax.l_return  in
          let uu____3782 =
            let uu____3786 = to_str combs.FStar_Syntax_Syntax.l_bind  in
            let uu____3788 =
              let uu____3792 = to_str combs.FStar_Syntax_Syntax.l_subcomp  in
              let uu____3794 =
                let uu____3798 =
                  to_str combs.FStar_Syntax_Syntax.l_if_then_else  in
                [uu____3798]  in
              uu____3792 :: uu____3794  in
            uu____3786 :: uu____3788  in
          uu____3780 :: uu____3782  in
        uu____3774 :: uu____3776  in
      uu____3768 :: uu____3770  in
    FStar_Util.format
      "{\nl_base_effect = %s\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  }\n"
      uu____3764
  
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___14_3814  ->
    match uu___14_3814 with
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
          let uu____3847 =
            let uu____3849 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3849  in
          if uu____3847
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
               let uu____3870 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3870 (FStar_String.concat ",\n\t")
                in
             let eff_name =
               let uu____3887 = FStar_Syntax_Util.is_layered ed  in
               if uu____3887 then "layered_effect" else "new_effect"  in
             let uu____3895 =
               let uu____3899 =
                 let uu____3903 =
                   let uu____3907 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname  in
                   let uu____3909 =
                     let uu____3913 =
                       let uu____3915 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs
                          in
                       FStar_All.pipe_left enclose_universes uu____3915  in
                     let uu____3919 =
                       let uu____3923 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders
                          in
                       let uu____3926 =
                         let uu____3930 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature
                            in
                         let uu____3932 =
                           let uu____3936 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____3938 =
                             let uu____3942 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions
                                in
                             [uu____3942]  in
                           uu____3936 :: uu____3938  in
                         uu____3930 :: uu____3932  in
                       uu____3923 :: uu____3926  in
                     uu____3913 :: uu____3919  in
                   uu____3907 :: uu____3909  in
                 (if for_free then "_for_free " else "") :: uu____3903  in
               eff_name :: uu____3899  in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu____3895)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se  ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
        let uu____3994 = FStar_All.pipe_right ts_opt FStar_Util.must  in
        FStar_All.pipe_right uu____3994 tscheme_to_string
      else "<None>"  in
    let uu____4001 = lid_to_string se.FStar_Syntax_Syntax.source  in
    let uu____4003 = lid_to_string se.FStar_Syntax_Syntax.target  in
    let uu____4005 = tsopt_to_string se.FStar_Syntax_Syntax.lift  in
    let uu____4007 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp  in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____4001 uu____4003 uu____4005 uu____4007
  
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
          (lid,univs1,tps,k,uu____4042,uu____4043) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4059 = FStar_Options.print_universes ()  in
          if uu____4059
          then
            let uu____4063 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____4063 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____4072,uu____4073,uu____4074) ->
          let uu____4081 = FStar_Options.print_universes ()  in
          if uu____4081
          then
            let uu____4085 = univ_names_to_string univs1  in
            let uu____4087 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4085
              lid.FStar_Ident.str uu____4087
          else
            (let uu____4092 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____4092)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____4098 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4100 =
            let uu____4102 = FStar_Options.print_universes ()  in
            if uu____4102
            then
              let uu____4106 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____4106
            else ""  in
          let uu____4112 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4098
            lid.FStar_Ident.str uu____4100 uu____4112
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4118 = FStar_Options.print_universes ()  in
          if uu____4118
          then
            let uu____4122 = univ_names_to_string us  in
            let uu____4124 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____4122 uu____4124
          else
            (let uu____4129 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4129)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4133) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4139 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____4139
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4143) ->
          let uu____4152 =
            let uu____4154 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4154 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____4152
      | FStar_Syntax_Syntax.Sig_fail (errs,lax1,ses) ->
          let uu____4180 = FStar_Util.string_of_bool lax1  in
          let uu____4182 =
            FStar_Common.string_of_list FStar_Util.string_of_int errs  in
          let uu____4185 =
            let uu____4187 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4187 (FStar_String.concat "\n")  in
          FStar_Util.format3 "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n"
            uu____4180 uu____4182 uu____4185
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4199 = FStar_Syntax_Util.is_dm4f ed  in
          eff_decl_to_string' uu____4199 x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____4211 = FStar_Options.print_universes ()  in
          if uu____4211
          then
            let uu____4215 =
              let uu____4220 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____4220  in
            (match uu____4215 with
             | (univs2,t) ->
                 let uu____4234 =
                   let uu____4239 =
                     let uu____4240 = FStar_Syntax_Subst.compress t  in
                     uu____4240.FStar_Syntax_Syntax.n  in
                   match uu____4239 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4269 -> failwith "impossible"  in
                 (match uu____4234 with
                  | (tps1,c1) ->
                      let uu____4278 = sli l  in
                      let uu____4280 = univ_names_to_string univs2  in
                      let uu____4282 = binders_to_string " " tps1  in
                      let uu____4285 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4278
                        uu____4280 uu____4282 uu____4285))
          else
            (let uu____4290 = sli l  in
             let uu____4292 = binders_to_string " " tps  in
             let uu____4295 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4290 uu____4292
               uu____4295)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4304 =
            let uu____4306 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4306  in
          let uu____4316 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4304 uu____4316
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n1,p,t,ty) ->
          let uu____4324 = FStar_Ident.string_of_lid m  in
          let uu____4326 = FStar_Ident.string_of_lid n1  in
          let uu____4328 = FStar_Ident.string_of_lid p  in
          let uu____4330 = tscheme_to_string t  in
          let uu____4332 = tscheme_to_string ty  in
          FStar_Util.format5 "polymonadic_bind (%s, %s) |> %s = (%s, %s)"
            uu____4324 uu____4326 uu____4328 uu____4330 uu____4332
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4338 ->
        let uu____4341 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____4341 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____4358 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4358 msg
  
let (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4369,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4371;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4373;
                       FStar_Syntax_Syntax.lbdef = uu____4374;
                       FStar_Syntax_Syntax.lbattrs = uu____4375;
                       FStar_Syntax_Syntax.lbpos = uu____4376;_}::[]),uu____4377)
        ->
        let uu____4400 = lbname_to_string lb  in
        let uu____4402 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4400 uu____4402
    | uu____4405 ->
        let uu____4406 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____4406 (FStar_String.concat ", ")
  
let (tag_of_sigelt : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4432 -> "Sig_inductive_typ"
    | FStar_Syntax_Syntax.Sig_bundle uu____4450 -> "Sig_bundle"
    | FStar_Syntax_Syntax.Sig_datacon uu____4460 -> "Sig_datacon"
    | FStar_Syntax_Syntax.Sig_declare_typ uu____4477 -> "Sig_declare_typ"
    | FStar_Syntax_Syntax.Sig_let uu____4485 -> "Sig_let"
    | FStar_Syntax_Syntax.Sig_main uu____4493 -> "Sig_main"
    | FStar_Syntax_Syntax.Sig_assume uu____4495 -> "Sig_assume"
    | FStar_Syntax_Syntax.Sig_new_effect uu____4503 -> "Sig_new_effect"
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4505 -> "Sig_sub_effect"
    | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4507 -> "Sig_effect_abbrev"
    | FStar_Syntax_Syntax.Sig_pragma uu____4521 -> "Sig_pragma"
    | FStar_Syntax_Syntax.Sig_splice uu____4523 -> "Sig_splice"
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____4531 ->
        "Sig_polymonadic_bind"
    | FStar_Syntax_Syntax.Sig_fail uu____4543 -> "Sig_fail"
  
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4564 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4566 =
      let uu____4568 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4568 (FStar_String.concat "\n")  in
    let uu____4578 =
      let uu____4580 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4580 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4564
      uu____4566 uu____4578
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
           (let uu____4630 = f x  in
            FStar_Util.string_builder_append strb uu____4630);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4639 = f x1  in
                 FStar_Util.string_builder_append strb uu____4639)) xs;
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
           (let uu____4686 = f x  in
            FStar_Util.string_builder_append strb uu____4686);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4695 = f x1  in
                 FStar_Util.string_builder_append strb uu____4695)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____4717 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4717
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___15_4730  ->
    match uu___15_4730 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4746 =
          let uu____4748 =
            let uu____4750 =
              let uu____4752 =
                let uu____4754 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4754 (FStar_String.concat " ")  in
              Prims.op_Hat uu____4752 ")"  in
            Prims.op_Hat " " uu____4750  in
          Prims.op_Hat h uu____4748  in
        Prims.op_Hat "(" uu____4746
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4769 =
          let uu____4771 = emb_typ_to_string a  in
          let uu____4773 =
            let uu____4775 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____4775  in
          Prims.op_Hat uu____4771 uu____4773  in
        Prims.op_Hat "(" uu____4769
  