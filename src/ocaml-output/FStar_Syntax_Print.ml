open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___212_6  ->
    match uu___212_6 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____10 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_constant_at_level " uu____10
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____15 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_equational_at_level " uu____15
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____19 =
          let uu____21 = delta_depth_to_string d  in
          Prims.strcat uu____21 ")"  in
        Prims.strcat "Delta_abstract (" uu____19
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____33 = FStar_Options.print_real_names ()  in
    if uu____33
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____60 =
      let uu____62 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____62  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____60
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____72 = FStar_Options.print_real_names ()  in
    if uu____72
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____85 =
      let uu____87 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____87  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____85
  
let (infix_prim_ops :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
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
let (unary_prim_ops :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
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
      | uu____309 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____322 -> failwith "get_lid"
  
let (is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
  
let (is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
  
let (quants :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
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
  'Auu____425 'Auu____426 .
    ('Auu____425,'Auu____426) FStar_Util.either -> Prims.bool
  =
  fun uu___213_436  ->
    match uu___213_436 with
    | FStar_Util.Inl uu____441 -> false
    | FStar_Util.Inr uu____443 -> true
  
let filter_imp :
  'Auu____450 .
    ('Auu____450,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____450,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___214_505  ->
            match uu___214_505 with
            | (uu____513,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____520,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____521)) -> false
            | (uu____526,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____527)) -> false
            | uu____533 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____551 =
      let uu____552 = FStar_Syntax_Subst.compress e  in
      uu____552.FStar_Syntax_Syntax.n  in
    match uu____551 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____613 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____613
        then
          let uu____622 =
            let uu____627 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____627  in
          (match uu____622 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____638 =
                 let uu____641 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____641 :: xs  in
               FStar_Pervasives_Native.Some uu____638
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____653 ->
        let uu____654 = is_lex_top e  in
        if uu____654
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____702 = f hd1  in if uu____702 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____734 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____734
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____765 = get_lid e  in find_lid uu____765 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____777 = get_lid e  in find_lid uu____777 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____789 = get_lid t  in find_lid uu____789 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___215_803  ->
    match uu___215_803 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____814 = FStar_Options.hide_uvar_nums ()  in
    if uu____814
    then "?"
    else
      (let uu____821 =
         let uu____823 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____823 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____821)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____835 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____837 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____835 uu____837
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
     FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun u  ->
    let uu____863 = FStar_Options.hide_uvar_nums ()  in
    if uu____863
    then "?"
    else
      (let uu____870 =
         let uu____872 =
           let uu____874 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____874 FStar_Util.string_of_int  in
         let uu____878 =
           let uu____880 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____880  in
         Prims.strcat uu____872 uu____878  in
       Prims.strcat "?" uu____870)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____908 = FStar_Syntax_Subst.compress_univ u  in
      match uu____908 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____921 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____932 = FStar_Syntax_Subst.compress_univ u  in
    match uu____932 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____943 = univ_uvar_to_string u1  in
        Prims.strcat "U_unif " uu____943
    | FStar_Syntax_Syntax.U_name x ->
        Prims.strcat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____950 = FStar_Util.string_of_int x  in
        Prims.strcat "@" uu____950
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____955 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____955 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____976 = univ_to_string u2  in
             let uu____978 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____976 uu____978)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____984 =
          let uu____986 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____986 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____984
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____1005 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____1005 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____1022 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____1022 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___216_1040  ->
    match uu___216_1040 with
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
        let uu____1056 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____1056
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1061 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____1061
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1074 =
          let uu____1076 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1076  in
        let uu____1077 =
          let uu____1079 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1079 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____1074 uu____1077
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1105 =
          let uu____1107 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1107  in
        let uu____1108 =
          let uu____1110 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1110 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1105 uu____1108
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1127 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____1127
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
    | uu____1150 ->
        let uu____1153 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____1153 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1181 ->
        let uu____1184 = quals_to_string quals  in
        Prims.strcat uu____1184 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1387 = db_to_string x  in
        Prims.strcat "Tm_bvar: " uu____1387
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1391 = nm_to_string x  in
        Prims.strcat "Tm_name: " uu____1391
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1395 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____1395
    | FStar_Syntax_Syntax.Tm_uinst uu____1398 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1406 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1408 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1410,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1411;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1425,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1426;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1440 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1460 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1476 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1484 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1502 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1526 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1554 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1569 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1583,m) ->
        let uu____1621 = FStar_ST.op_Bang m  in
        (match uu____1621 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1679 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1685,m) ->
        let uu____1691 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1691
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1695 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1698 =
      let uu____1700 = FStar_Options.ugly ()  in Prims.op_Negation uu____1700
       in
    if uu____1698
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1714 = FStar_Options.print_implicits ()  in
         if uu____1714 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1722 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1747,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1773,thunk);
             FStar_Syntax_Syntax.ltyp = uu____1775;
             FStar_Syntax_Syntax.rng = uu____1776;_}
           ->
           let uu____1787 =
             let uu____1789 =
               let uu____1791 = FStar_Common.force_thunk thunk  in
               term_to_string uu____1791  in
             Prims.strcat uu____1789 "]"  in
           Prims.strcat "[LAZYEMB:" uu____1787
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1837 =
             let uu____1839 =
               let uu____1841 =
                 let uu____1842 =
                   let uu____1851 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1851  in
                 uu____1842 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1841  in
             Prims.strcat uu____1839 "]"  in
           Prims.strcat "[lazy:" uu____1837
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1920 =
                  match uu____1920 with
                  | (bv,t) ->
                      let uu____1928 = bv_to_string bv  in
                      let uu____1930 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1928 uu____1930
                   in
                let uu____1933 = term_to_string tm  in
                let uu____1935 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1933 uu____1935
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1944 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1944)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1967 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____2004 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____2029  ->
                                 match uu____2029 with
                                 | (t1,uu____2038) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____2004
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1967 (FStar_String.concat "\\/")  in
           let uu____2053 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____2053
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____2067 = tag_of_term t  in
           let uu____2069 = sli m  in
           let uu____2071 = term_to_string t'  in
           let uu____2073 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____2067 uu____2069
             uu____2071 uu____2073
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____2088 = tag_of_term t  in
           let uu____2090 = term_to_string t'  in
           let uu____2092 = sli m0  in
           let uu____2094 = sli m1  in
           let uu____2096 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2088
             uu____2090 uu____2092 uu____2094 uu____2096
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____2111 = FStar_Range.string_of_range r  in
           let uu____2113 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2111
             uu____2113
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2122 = lid_to_string l  in
           let uu____2124 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____2126 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2122 uu____2124
             uu____2126
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____2130) ->
           let uu____2135 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2135
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2139 = db_to_string x3  in
           let uu____2141 =
             let uu____2143 =
               let uu____2145 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____2145 ")"  in
             Prims.strcat ":(" uu____2143  in
           Prims.strcat uu____2139 uu____2141
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2152)) ->
           let uu____2167 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2167
           then ctx_uvar_to_string u
           else
             (let uu____2173 =
                let uu____2175 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2175  in
              Prims.strcat "?" uu____2173)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2198 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2198
           then
             let uu____2202 = ctx_uvar_to_string u  in
             let uu____2204 =
               let uu____2206 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2206 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2202 uu____2204
           else
             (let uu____2225 =
                let uu____2227 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2227  in
              Prims.strcat "?" uu____2225)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2234 = FStar_Options.print_universes ()  in
           if uu____2234
           then
             let uu____2238 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2238
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2266 = binders_to_string " -> " bs  in
           let uu____2269 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2266 uu____2269
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2301 = binders_to_string " " bs  in
                let uu____2304 = term_to_string t2  in
                let uu____2306 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2315 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2315)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2301 uu____2304
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____2306
            | uu____2319 ->
                let uu____2322 = binders_to_string " " bs  in
                let uu____2325 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2322 uu____2325)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2334 = bv_to_string xt  in
           let uu____2336 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2339 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2334 uu____2336 uu____2339
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2371 = term_to_string t  in
           let uu____2373 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2371 uu____2373
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2396 = lbs_to_string [] lbs  in
           let uu____2398 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2396 uu____2398
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2463 =
                   let uu____2465 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____2465
                     (FStar_Util.dflt "default")
                    in
                 let uu____2476 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2463 uu____2476
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2497 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2497
              in
           let uu____2500 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2500 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____2541 = term_to_string head1  in
           let uu____2543 =
             let uu____2545 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____2578  ->
                       match uu____2578 with
                       | (p,wopt,e) ->
                           let uu____2595 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____2598 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____2603 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____2603
                              in
                           let uu____2607 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____2595
                             uu____2598 uu____2607))
                in
             FStar_Util.concat_l "\n\t|" uu____2545  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2541 uu____2543
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2619 = FStar_Options.print_universes ()  in
           if uu____2619
           then
             let uu____2623 = term_to_string t  in
             let uu____2625 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2623 uu____2625
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2632 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2635 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2637 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2632 uu____2635
      uu____2637

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___217_2640  ->
    match uu___217_2640 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2646 = FStar_Util.string_of_int i  in
        let uu____2648 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2646 uu____2648
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2655 = bv_to_string x  in
        let uu____2657 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2655 uu____2657
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2666 = bv_to_string x  in
        let uu____2668 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2666 uu____2668
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2675 = FStar_Util.string_of_int i  in
        let uu____2677 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2675 uu____2677
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2684 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2684

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2688 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2688 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2704 =
      let uu____2706 = FStar_Options.ugly ()  in Prims.op_Negation uu____2706
       in
    if uu____2704
    then
      let e =
        let uu____2711 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2711  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2740 = fv_to_string l  in
           let uu____2742 =
             let uu____2744 =
               FStar_List.map
                 (fun uu____2758  ->
                    match uu____2758 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2744 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2740 uu____2742
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2783) ->
           let uu____2788 = FStar_Options.print_bound_var_types ()  in
           if uu____2788
           then
             let uu____2792 = bv_to_string x1  in
             let uu____2794 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2792 uu____2794
           else
             (let uu____2799 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2799)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2803 = FStar_Options.print_bound_var_types ()  in
           if uu____2803
           then
             let uu____2807 = bv_to_string x1  in
             let uu____2809 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2807 uu____2809
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2816 = FStar_Options.print_bound_var_types ()  in
           if uu____2816
           then
             let uu____2820 = bv_to_string x1  in
             let uu____2822 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2820 uu____2822
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2838 = quals_to_string' quals  in
      let uu____2840 =
        let uu____2842 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2862 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2864 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2866 =
                    let uu____2868 = FStar_Options.print_universes ()  in
                    if uu____2868
                    then
                      let uu____2872 =
                        let uu____2874 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2874 ">"  in
                      Prims.strcat "<" uu____2872
                    else ""  in
                  let uu____2881 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2883 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2862
                    uu____2864 uu____2866 uu____2881 uu____2883))
           in
        FStar_Util.concat_l "\n and " uu____2842  in
      FStar_Util.format3 "%slet %s %s" uu____2838
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2840

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___218_2898  ->
    match uu___218_2898 with
    | [] -> ""
    | tms ->
        let uu____2906 =
          let uu____2908 =
            FStar_List.map
              (fun t  ->
                 let uu____2916 = term_to_string t  in paren uu____2916) tms
             in
          FStar_All.pipe_right uu____2908 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2906

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2925 = FStar_Options.print_effect_args ()  in
    if uu____2925
    then
      let uu____2929 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2929
    else
      (let uu____2932 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2934 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2932 uu____2934)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___219_2938  ->
      match uu___219_2938 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.strcat "[|" (Prims.strcat s "|]")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____2956 =
            let uu____2958 = term_to_string t  in
            Prims.strcat uu____2958 (Prims.strcat "]" s)  in
          Prims.strcat "#[" uu____2956
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
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2978 =
        let uu____2980 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2980  in
      if uu____2978
      then
        let uu____2984 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2984 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2995 = b  in
         match uu____2995 with
         | (a,imp) ->
             let uu____3009 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____3009
             then
               let uu____3013 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____3013
             else
               (let uu____3018 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____3021 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____3021)
                   in
                if uu____3018
                then
                  let uu____3025 = nm_to_string a  in
                  imp_to_string uu____3025 imp
                else
                  (let uu____3029 =
                     let uu____3031 = nm_to_string a  in
                     let uu____3033 =
                       let uu____3035 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____3035  in
                     Prims.strcat uu____3031 uu____3033  in
                   imp_to_string uu____3029 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  = fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____3054 = FStar_Options.print_implicits ()  in
        if uu____3054 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____3065 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____3065 (FStar_String.concat sep)
      else
        (let uu____3093 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____3093 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___220_3107  ->
    match uu___220_3107 with
    | (a,imp) ->
        let uu____3121 = term_to_string a  in imp_to_string uu____3121 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____3133 = FStar_Options.print_implicits ()  in
      if uu____3133 then args else filter_imp args  in
    let uu____3148 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____3148 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____3177 = FStar_Options.ugly ()  in
      if uu____3177
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____3188 =
      let uu____3190 = FStar_Options.ugly ()  in Prims.op_Negation uu____3190
       in
    if uu____3188
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____3211 =
             let uu____3212 = FStar_Syntax_Subst.compress t  in
             uu____3212.FStar_Syntax_Syntax.n  in
           (match uu____3211 with
            | FStar_Syntax_Syntax.Tm_type uu____3216 when
                let uu____3217 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3217 -> term_to_string t
            | uu____3219 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3222 = univ_to_string u  in
                     let uu____3224 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3222 uu____3224
                 | uu____3227 ->
                     let uu____3230 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3230))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3243 =
             let uu____3244 = FStar_Syntax_Subst.compress t  in
             uu____3244.FStar_Syntax_Syntax.n  in
           (match uu____3243 with
            | FStar_Syntax_Syntax.Tm_type uu____3248 when
                let uu____3249 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3249 -> term_to_string t
            | uu____3251 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3254 = univ_to_string u  in
                     let uu____3256 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3254 uu____3256
                 | uu____3259 ->
                     let uu____3262 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3262))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3268 = FStar_Options.print_effect_args ()  in
             if uu____3268
             then
               let uu____3272 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3274 =
                 let uu____3276 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3276 (FStar_String.concat ", ")
                  in
               let uu____3291 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3293 =
                 let uu____3295 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3295 (FStar_String.concat ", ")
                  in
               let uu____3322 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3272
                 uu____3274 uu____3291 uu____3293 uu____3322
             else
               (let uu____3327 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___221_3333  ->
                           match uu___221_3333 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3336 -> false)))
                    &&
                    (let uu____3339 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3339)
                   in
                if uu____3327
                then
                  let uu____3343 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3343
                else
                  (let uu____3348 =
                     ((let uu____3352 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3352) &&
                        (let uu____3355 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3355))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____3348
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3361 =
                        (let uu____3365 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3365) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___222_3371  ->
                                   match uu___222_3371 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3374 -> false)))
                         in
                      if uu____3361
                      then
                        let uu____3378 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3378
                      else
                        (let uu____3383 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3385 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3383 uu____3385))))
              in
           let dec =
             let uu____3390 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___223_3403  ->
                       match uu___223_3403 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3410 =
                             let uu____3412 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3412
                              in
                           [uu____3410]
                       | uu____3417 -> []))
                in
             FStar_All.pipe_right uu____3390 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____3436 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___224_3446  ->
    match uu___224_3446 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____3463 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3500 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3525  ->
                              match uu____3525 with
                              | (t,uu____3534) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3500
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3463 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3551 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3551
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3556) ->
        let uu____3561 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3561
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____3572 = sli m  in
        let uu____3574 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3572 uu____3574
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3584 = sli m  in
        let uu____3586 = sli m'  in
        let uu____3588 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3584
          uu____3586 uu____3588

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____3603 = FStar_Options.ugly ()  in
      if uu____3603
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
      let uu____3624 = b  in
      match uu____3624 with
      | (a,imp) ->
          let n1 =
            let uu____3632 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3632
            then FStar_Util.JsonNull
            else
              (let uu____3637 =
                 let uu____3639 = nm_to_string a  in
                 imp_to_string uu____3639 imp  in
               FStar_Util.JsonStr uu____3637)
             in
          let t =
            let uu____3642 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3642  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____3674 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3674
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3692 = FStar_Options.print_universes ()  in
    if uu____3692 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3708 =
      let uu____3710 = FStar_Options.ugly ()  in Prims.op_Negation uu____3710
       in
    if uu____3708
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____3720 = s  in
       match uu____3720 with
       | (us,t) ->
           let uu____3732 =
             let uu____3734 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3734  in
           let uu____3738 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3732 uu____3738)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3748 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3750 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3753 =
      let uu____3755 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3755  in
    let uu____3759 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3761 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3748 uu____3750 uu____3753
      uu____3759 uu____3761
  
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
          let uu____3792 =
            let uu____3794 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3794  in
          if uu____3792
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____3815 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3815 (FStar_String.concat ",\n\t")
                in
             let uu____3830 =
               let uu____3834 =
                 let uu____3838 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____3840 =
                   let uu____3844 =
                     let uu____3846 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____3846  in
                   let uu____3850 =
                     let uu____3854 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____3857 =
                       let uu____3861 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____3863 =
                         let uu____3867 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____3869 =
                           let uu____3873 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____3875 =
                             let uu____3879 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____3881 =
                               let uu____3885 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____3887 =
                                 let uu____3891 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____3893 =
                                   let uu____3897 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____3899 =
                                     let uu____3903 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____3905 =
                                       let uu____3909 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____3911 =
                                         let uu____3915 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____3917 =
                                           let uu____3921 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____3923 =
                                             let uu____3927 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____3929 =
                                               let uu____3933 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____3935 =
                                                 let uu____3939 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____3941 =
                                                   let uu____3945 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____3945]  in
                                                 uu____3939 :: uu____3941  in
                                               uu____3933 :: uu____3935  in
                                             uu____3927 :: uu____3929  in
                                           uu____3921 :: uu____3923  in
                                         uu____3915 :: uu____3917  in
                                       uu____3909 :: uu____3911  in
                                     uu____3903 :: uu____3905  in
                                   uu____3897 :: uu____3899  in
                                 uu____3891 :: uu____3893  in
                               uu____3885 :: uu____3887  in
                             uu____3879 :: uu____3881  in
                           uu____3873 :: uu____3875  in
                         uu____3867 :: uu____3869  in
                       uu____3861 :: uu____3863  in
                     uu____3854 :: uu____3857  in
                   uu____3844 :: uu____3850  in
                 uu____3838 :: uu____3840  in
               (if for_free then "_for_free " else "") :: uu____3834  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____3830)
  
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
          (lid,univs1,tps,k,uu____4019,uu____4020) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4036 = FStar_Options.print_universes ()  in
          if uu____4036
          then
            let uu____4040 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____4040 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____4049,uu____4050,uu____4051) ->
          let uu____4058 = FStar_Options.print_universes ()  in
          if uu____4058
          then
            let uu____4062 = univ_names_to_string univs1  in
            let uu____4064 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4062
              lid.FStar_Ident.str uu____4064
          else
            (let uu____4069 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____4069)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____4075 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4077 =
            let uu____4079 = FStar_Options.print_universes ()  in
            if uu____4079
            then
              let uu____4083 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____4083
            else ""  in
          let uu____4089 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4075
            lid.FStar_Ident.str uu____4077 uu____4089
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4095 = FStar_Options.print_universes ()  in
          if uu____4095
          then
            let uu____4099 = univ_names_to_string us  in
            let uu____4101 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____4099 uu____4101
          else
            (let uu____4106 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____4106)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4110) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____4116 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____4116
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4120) ->
          let uu____4129 =
            let uu____4131 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4131 (FStar_String.concat "\n")  in
          Prims.strcat "(* Sig_bundle *)" uu____4129
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____4176) -> lift_wp
            | (uu____4183,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____4191 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____4191 with
           | (us,t) ->
               let uu____4203 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____4205 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____4207 = univ_names_to_string us  in
               let uu____4209 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____4203
                 uu____4205 uu____4207 uu____4209)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
          let uu____4221 = FStar_Options.print_universes ()  in
          if uu____4221
          then
            let uu____4225 =
              let uu____4230 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____4230  in
            (match uu____4225 with
             | (univs2,t) ->
                 let uu____4244 =
                   let uu____4249 =
                     let uu____4250 = FStar_Syntax_Subst.compress t  in
                     uu____4250.FStar_Syntax_Syntax.n  in
                   match uu____4249 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4279 -> failwith "impossible"  in
                 (match uu____4244 with
                  | (tps1,c1) ->
                      let uu____4288 = sli l  in
                      let uu____4290 = univ_names_to_string univs2  in
                      let uu____4292 = binders_to_string " " tps1  in
                      let uu____4295 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4288
                        uu____4290 uu____4292 uu____4295))
          else
            (let uu____4300 = sli l  in
             let uu____4302 = binders_to_string " " tps  in
             let uu____4305 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4300 uu____4302
               uu____4305)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4314 =
            let uu____4316 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4316  in
          let uu____4326 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4314 uu____4326
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____4330 ->
        let uu____4333 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.strcat uu____4333 (Prims.strcat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____4350 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4350 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4361,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4363;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4365;
                       FStar_Syntax_Syntax.lbdef = uu____4366;
                       FStar_Syntax_Syntax.lbattrs = uu____4367;
                       FStar_Syntax_Syntax.lbpos = uu____4368;_}::[]),uu____4369)
        ->
        let uu____4392 = lbname_to_string lb  in
        let uu____4394 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4392 uu____4394
    | uu____4397 ->
        let uu____4398 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____4398 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4422 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4424 =
      let uu____4426 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4426 (FStar_String.concat "\n")  in
    let uu____4436 =
      let uu____4438 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4438 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4422
      uu____4424 uu____4436
  
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
          (let uu____4482 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____4482))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____4491 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____4491)));
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
           (let uu____4532 = f x  in
            FStar_Util.string_builder_append strb uu____4532);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4541 = f x1  in
                 FStar_Util.string_builder_append strb uu____4541)) xs;
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
           (let uu____4588 = f x  in
            FStar_Util.string_builder_append strb uu____4588);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4597 = f x1  in
                 FStar_Util.string_builder_append strb uu____4597)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____4619 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4619
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___225_4632  ->
    match uu___225_4632 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4648 =
          let uu____4650 =
            let uu____4652 =
              let uu____4654 =
                let uu____4656 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4656 (FStar_String.concat " ")  in
              Prims.strcat uu____4654 ")"  in
            Prims.strcat " " uu____4652  in
          Prims.strcat h uu____4650  in
        Prims.strcat "(" uu____4648
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4671 =
          let uu____4673 = emb_typ_to_string a  in
          let uu____4675 =
            let uu____4677 = emb_typ_to_string b  in
            Prims.strcat ") -> " uu____4677  in
          Prims.strcat uu____4673 uu____4675  in
        Prims.strcat "(" uu____4671
  