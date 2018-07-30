open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___204_5  ->
    match uu___204_5 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____7 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_constant_at_level " uu____7
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____9 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_equational_at_level " uu____9
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____11 =
          let uu____12 = delta_depth_to_string d  in
          Prims.strcat uu____12 ")"  in
        Prims.strcat "Delta_abstract (" uu____11
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____18 = FStar_Options.print_real_names ()  in
    if uu____18
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____35 =
      let uu____36 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____36  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____35
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____42 = FStar_Options.print_real_names ()  in
    if uu____42
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____49 =
      let uu____50 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____50  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____49
  
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
      | uu____188 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____199 -> failwith "get_lid"
  
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
  'Auu____271 'Auu____272 .
    ('Auu____271,'Auu____272) FStar_Util.either -> Prims.bool
  =
  fun uu___205_281  ->
    match uu___205_281 with
    | FStar_Util.Inl uu____286 -> false
    | FStar_Util.Inr uu____287 -> true
  
let filter_imp :
  'Auu____292 .
    ('Auu____292,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____292,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___206_347  ->
            match uu___206_347 with
            | (uu____354,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____355)) -> false
            | uu____358 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____374 =
      let uu____375 = FStar_Syntax_Subst.compress e  in
      uu____375.FStar_Syntax_Syntax.n  in
    match uu____374 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____436 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____436
        then
          let uu____441 =
            let uu____446 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____446  in
          (match uu____441 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____456 =
                 let uu____459 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____459 :: xs  in
               FStar_Pervasives_Native.Some uu____456
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____469 ->
        let uu____470 = is_lex_top e  in
        if uu____470
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____511 = f hd1  in if uu____511 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____535 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____535
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____559 = get_lid e  in find_lid uu____559 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____569 = get_lid e  in find_lid uu____569 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____579 = get_lid t  in find_lid uu____579 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___207_589  ->
    match uu___207_589 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____597 = FStar_Options.hide_uvar_nums ()  in
    if uu____597
    then "?"
    else
      (let uu____599 =
         let uu____600 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____600 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____599)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____606 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____607 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____606 uu____607
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
     FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun u  ->
    let uu____629 = FStar_Options.hide_uvar_nums ()  in
    if uu____629
    then "?"
    else
      (let uu____631 =
         let uu____632 =
           let uu____633 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____633 FStar_Util.string_of_int  in
         let uu____634 =
           let uu____635 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____635  in
         Prims.strcat uu____632 uu____634  in
       Prims.strcat "?" uu____631)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____656 = FStar_Syntax_Subst.compress_univ u  in
      match uu____656 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____666 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____674 = FStar_Syntax_Subst.compress_univ u  in
    match uu____674 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____684 = univ_uvar_to_string u1  in
        Prims.strcat "U_unif " uu____684
    | FStar_Syntax_Syntax.U_name x ->
        Prims.strcat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____687 = FStar_Util.string_of_int x  in
        Prims.strcat "@" uu____687
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____689 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____689 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____703 = univ_to_string u2  in
             let uu____704 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____703 uu____704)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____708 =
          let uu____709 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____709 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____708
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____719 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____719 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____729 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____729 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___208_740  ->
    match uu___208_740 with
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
        let uu____742 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____742
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____745 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____745 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____756 =
          let uu____757 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____757  in
        let uu____758 =
          let uu____759 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____759 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____756 uu____758
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____778 =
          let uu____779 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____779  in
        let uu____780 =
          let uu____781 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____781 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____778 uu____780
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____791 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____791
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
    | uu____802 ->
        let uu____805 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____805 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____823 ->
        let uu____826 = quals_to_string quals  in Prims.strcat uu____826 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____970 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____970
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____972 = nm_to_string x  in Prims.strcat "Tm_name: " uu____972
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____974 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____974
    | FStar_Syntax_Syntax.Tm_uinst uu____975 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____982 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____983 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____984,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____985;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____998,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_dynamic ;
                     FStar_Syntax_Syntax.antiquotes = uu____999;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1012 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1031 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1046 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1053 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1070 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1093 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1120 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1133 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1146,m) ->
        let uu____1184 = FStar_ST.op_Bang m  in
        (match uu____1184 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1240 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1245,m) ->
        let uu____1251 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1251
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1252 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1254 =
      let uu____1255 = FStar_Options.ugly ()  in Prims.op_Negation uu____1255
       in
    if uu____1254
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1263 = FStar_Options.print_implicits ()  in
         if uu____1263 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1267 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1290,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1314,thunk);
             FStar_Syntax_Syntax.ltyp = uu____1316;
             FStar_Syntax_Syntax.rng = uu____1317;_}
           ->
           let uu____1328 =
             let uu____1329 =
               let uu____1330 = FStar_Common.force_thunk thunk  in
               term_to_string uu____1330  in
             Prims.strcat uu____1329 "]"  in
           Prims.strcat "[LAZYEMB:" uu____1328
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1374 =
             let uu____1375 =
               let uu____1376 =
                 let uu____1377 =
                   let uu____1386 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1386  in
                 uu____1377 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1376  in
             Prims.strcat uu____1375 "]"  in
           Prims.strcat "[lazy:" uu____1374
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1451 =
                  match uu____1451 with
                  | (bv,t) ->
                      let uu____1458 = bv_to_string bv  in
                      let uu____1459 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1458 uu____1459
                   in
                let uu____1460 = term_to_string tm  in
                let uu____1461 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1460 uu____1461
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1468 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1468)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1488 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1522 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1544  ->
                                 match uu____1544 with
                                 | (t1,uu____1552) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1522
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1488 (FStar_String.concat "\\/")  in
           let uu____1561 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1561
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1573 = tag_of_term t  in
           let uu____1574 = sli m  in
           let uu____1575 = term_to_string t'  in
           let uu____1576 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1573 uu____1574
             uu____1575 uu____1576
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1589 = tag_of_term t  in
           let uu____1590 = term_to_string t'  in
           let uu____1591 = sli m0  in
           let uu____1592 = sli m1  in
           let uu____1593 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1589
             uu____1590 uu____1591 uu____1592 uu____1593
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1602 = FStar_Range.string_of_range r  in
           let uu____1603 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1602
             uu____1603
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1610 = lid_to_string l  in
           let uu____1611 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1612 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1610 uu____1611
             uu____1612
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1614) ->
           let uu____1619 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1619
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1621 = db_to_string x3  in
           let uu____1622 =
             let uu____1623 =
               let uu____1624 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1624 ")"  in
             Prims.strcat ":(" uu____1623  in
           Prims.strcat uu____1621 uu____1622
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1628)) ->
           let uu____1643 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1643
           then ctx_uvar_to_string u
           else
             (let uu____1645 =
                let uu____1646 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1646  in
              Prims.strcat "?" uu____1645)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1665 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1665
           then
             let uu____1666 = ctx_uvar_to_string u  in
             let uu____1667 =
               let uu____1668 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1668 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1666 uu____1667
           else
             (let uu____1680 =
                let uu____1681 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1681  in
              Prims.strcat "?" uu____1680)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1684 = FStar_Options.print_universes ()  in
           if uu____1684
           then
             let uu____1685 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1685
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1709 = binders_to_string " -> " bs  in
           let uu____1710 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1709 uu____1710
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1739 = binders_to_string " " bs  in
                let uu____1740 = term_to_string t2  in
                let uu____1741 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1745 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1745)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1739 uu____1740
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1741
            | uu____1748 ->
                let uu____1751 = binders_to_string " " bs  in
                let uu____1752 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1751 uu____1752)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1759 = bv_to_string xt  in
           let uu____1760 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1761 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1759 uu____1760 uu____1761
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1790 = term_to_string t  in
           let uu____1791 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1790 uu____1791
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1810 = lbs_to_string [] lbs  in
           let uu____1811 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1810 uu____1811
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1872 =
                   let uu____1873 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1873
                     (FStar_Util.dflt "default")
                    in
                 let uu____1878 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1872 uu____1878
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1894 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1894
              in
           let uu____1895 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1895 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1934 = term_to_string head1  in
           let uu____1935 =
             let uu____1936 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1966  ->
                       match uu____1966 with
                       | (p,wopt,e) ->
                           let uu____1982 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1983 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1985 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1985
                              in
                           let uu____1986 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1982
                             uu____1983 uu____1986))
                in
             FStar_Util.concat_l "\n\t|" uu____1936  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1934 uu____1935
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1993 = FStar_Options.print_universes ()  in
           if uu____1993
           then
             let uu____1994 = term_to_string t  in
             let uu____1995 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1994 uu____1995
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1998 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1999 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2000 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1998 uu____1999
      uu____2000

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___209_2001  ->
    match uu___209_2001 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2004 = FStar_Util.string_of_int i  in
        let uu____2005 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2004 uu____2005
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2008 = bv_to_string x  in
        let uu____2009 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2008 uu____2009
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2016 = bv_to_string x  in
        let uu____2017 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2016 uu____2017
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2020 = FStar_Util.string_of_int i  in
        let uu____2021 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2020 uu____2021
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2024 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2024

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2026 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2026 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2036 =
      let uu____2037 = FStar_Options.ugly ()  in Prims.op_Negation uu____2037
       in
    if uu____2036
    then
      let e =
        let uu____2039 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2039  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2062 = fv_to_string l  in
           let uu____2063 =
             let uu____2064 =
               FStar_List.map
                 (fun uu____2075  ->
                    match uu____2075 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2064 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2062 uu____2063
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2087) ->
           let uu____2092 = FStar_Options.print_bound_var_types ()  in
           if uu____2092
           then
             let uu____2093 = bv_to_string x1  in
             let uu____2094 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2093 uu____2094
           else
             (let uu____2096 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2096)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2098 = FStar_Options.print_bound_var_types ()  in
           if uu____2098
           then
             let uu____2099 = bv_to_string x1  in
             let uu____2100 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2099 uu____2100
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2104 = FStar_Options.print_real_names ()  in
           if uu____2104
           then
             let uu____2105 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2105
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2117 = quals_to_string' quals  in
      let uu____2118 =
        let uu____2119 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2135 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2136 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2137 =
                    let uu____2138 = FStar_Options.print_universes ()  in
                    if uu____2138
                    then
                      let uu____2139 =
                        let uu____2140 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2140 ">"  in
                      Prims.strcat "<" uu____2139
                    else ""  in
                  let uu____2142 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2143 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2135
                    uu____2136 uu____2137 uu____2142 uu____2143))
           in
        FStar_Util.concat_l "\n and " uu____2119  in
      FStar_Util.format3 "%slet %s %s" uu____2117
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2118

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___210_2147  ->
    match uu___210_2147 with
    | [] -> ""
    | tms ->
        let uu____2153 =
          let uu____2154 =
            FStar_List.map
              (fun t  ->
                 let uu____2160 = term_to_string t  in paren uu____2160) tms
             in
          FStar_All.pipe_right uu____2154 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2153

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2164 = FStar_Options.print_effect_args ()  in
    if uu____2164
    then
      let uu____2165 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2165
    else
      (let uu____2167 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2168 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2167 uu____2168)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___211_2169  ->
    match uu___211_2169 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2170 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2173 = aqual_to_string aq  in Prims.strcat uu____2173 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2182 =
        let uu____2183 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2183  in
      if uu____2182
      then
        let uu____2184 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2184 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2190 = b  in
         match uu____2190 with
         | (a,imp) ->
             let uu____2203 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2203
             then
               let uu____2204 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2204
             else
               (let uu____2206 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2208 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2208)
                   in
                if uu____2206
                then
                  let uu____2209 = nm_to_string a  in
                  imp_to_string uu____2209 imp
                else
                  (let uu____2211 =
                     let uu____2212 = nm_to_string a  in
                     let uu____2213 =
                       let uu____2214 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2214  in
                     Prims.strcat uu____2212 uu____2213  in
                   imp_to_string uu____2211 imp)))

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
        let uu____2228 = FStar_Options.print_implicits ()  in
        if uu____2228 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2232 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2232 (FStar_String.concat sep)
      else
        (let uu____2254 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2254 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___212_2263  ->
    match uu___212_2263 with
    | (a,imp) ->
        let uu____2270 = term_to_string a  in imp_to_string uu____2270 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2279 = FStar_Options.print_implicits ()  in
      if uu____2279 then args else filter_imp args  in
    let uu____2289 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2289 (FStar_String.concat "; ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2308 = FStar_Options.ugly ()  in
      if uu____2308
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2313 =
      let uu____2314 = FStar_Options.ugly ()  in Prims.op_Negation uu____2314
       in
    if uu____2313
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2328 =
             let uu____2329 = FStar_Syntax_Subst.compress t  in
             uu____2329.FStar_Syntax_Syntax.n  in
           (match uu____2328 with
            | FStar_Syntax_Syntax.Tm_type uu____2332 when
                let uu____2333 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2333 -> term_to_string t
            | uu____2334 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2336 = univ_to_string u  in
                     let uu____2337 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2336 uu____2337
                 | uu____2338 ->
                     let uu____2341 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2341))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2352 =
             let uu____2353 = FStar_Syntax_Subst.compress t  in
             uu____2353.FStar_Syntax_Syntax.n  in
           (match uu____2352 with
            | FStar_Syntax_Syntax.Tm_type uu____2356 when
                let uu____2357 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2357 -> term_to_string t
            | uu____2358 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2360 = univ_to_string u  in
                     let uu____2361 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2360 uu____2361
                 | uu____2362 ->
                     let uu____2365 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2365))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2368 = FStar_Options.print_effect_args ()  in
             if uu____2368
             then
               let uu____2369 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2370 =
                 let uu____2371 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2371 (FStar_String.concat ", ")
                  in
               let uu____2380 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2381 =
                 let uu____2382 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2382 (FStar_String.concat ", ")
                  in
               let uu____2399 =
                 let uu____2400 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2400 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2369
                 uu____2370 uu____2380 uu____2381 uu____2399
             else
               (let uu____2410 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___213_2414  ->
                           match uu___213_2414 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2415 -> false)))
                    &&
                    (let uu____2417 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2417)
                   in
                if uu____2410
                then
                  let uu____2418 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2418
                else
                  (let uu____2420 =
                     ((let uu____2423 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2423) &&
                        (let uu____2425 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2425))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2420
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2427 =
                        (let uu____2430 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2430) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___214_2434  ->
                                   match uu___214_2434 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2435 -> false)))
                         in
                      if uu____2427
                      then
                        let uu____2436 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2436
                      else
                        (let uu____2438 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2439 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2438 uu____2439))))
              in
           let dec =
             let uu____2441 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___215_2451  ->
                       match uu___215_2451 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2457 =
                             let uu____2458 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2458
                              in
                           [uu____2457]
                       | uu____2459 -> []))
                in
             FStar_All.pipe_right uu____2441 (FStar_String.concat " ")  in
           FStar_Util.format2 "%s%s" basic dec)

and (cflags_to_string : FStar_Syntax_Syntax.cflags -> Prims.string) =
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
    | FStar_Syntax_Syntax.DECREASES uu____2463 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___216_2469  ->
    match uu___216_2469 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2484 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2518 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2540  ->
                              match uu____2540 with
                              | (t,uu____2548) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2518
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2484 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2558 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2558
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2561) ->
        let uu____2562 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2562
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2570 = sli m  in
        let uu____2571 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2570 uu____2571
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2579 = sli m  in
        let uu____2580 = sli m'  in
        let uu____2581 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2579
          uu____2580 uu____2581

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2592 = FStar_Options.ugly ()  in
      if uu____2592
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
      let uu____2606 = b  in
      match uu____2606 with
      | (a,imp) ->
          let n1 =
            let uu____2614 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2614
            then FStar_Util.JsonNull
            else
              (let uu____2616 =
                 let uu____2617 = nm_to_string a  in
                 imp_to_string uu____2617 imp  in
               FStar_Util.JsonStr uu____2616)
             in
          let t =
            let uu____2619 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2619  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2642 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2642
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2656 = FStar_Options.print_universes ()  in
    if uu____2656 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2663 =
      let uu____2664 = FStar_Options.ugly ()  in Prims.op_Negation uu____2664
       in
    if uu____2663
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2668 = s  in
       match uu____2668 with
       | (us,t) ->
           let uu____2679 =
             let uu____2680 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2680  in
           let uu____2681 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2679 uu____2681)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2687 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2688 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2689 =
      let uu____2690 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2690  in
    let uu____2691 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2692 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2687 uu____2688 uu____2689
      uu____2691 uu____2692
  
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
          let uu____2717 =
            let uu____2718 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2718  in
          if uu____2717
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2732 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2732 (FStar_String.concat ",\n\t")
                in
             let uu____2741 =
               let uu____2744 =
                 let uu____2747 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2748 =
                   let uu____2751 =
                     let uu____2752 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2752  in
                   let uu____2753 =
                     let uu____2756 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2757 =
                       let uu____2760 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2761 =
                         let uu____2764 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2765 =
                           let uu____2768 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2769 =
                             let uu____2772 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2773 =
                               let uu____2776 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2777 =
                                 let uu____2780 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2781 =
                                   let uu____2784 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2785 =
                                     let uu____2788 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2789 =
                                       let uu____2792 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2793 =
                                         let uu____2796 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2797 =
                                           let uu____2800 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2801 =
                                             let uu____2804 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2805 =
                                               let uu____2808 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2809 =
                                                 let uu____2812 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2813 =
                                                   let uu____2816 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2816]  in
                                                 uu____2812 :: uu____2813  in
                                               uu____2808 :: uu____2809  in
                                             uu____2804 :: uu____2805  in
                                           uu____2800 :: uu____2801  in
                                         uu____2796 :: uu____2797  in
                                       uu____2792 :: uu____2793  in
                                     uu____2788 :: uu____2789  in
                                   uu____2784 :: uu____2785  in
                                 uu____2780 :: uu____2781  in
                               uu____2776 :: uu____2777  in
                             uu____2772 :: uu____2773  in
                           uu____2768 :: uu____2769  in
                         uu____2764 :: uu____2765  in
                       uu____2760 :: uu____2761  in
                     uu____2756 :: uu____2757  in
                   uu____2751 :: uu____2753  in
                 uu____2747 :: uu____2748  in
               (if for_free then "_for_free " else "") :: uu____2744  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2741)
  
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
          (lid,univs1,tps,k,uu____2841,uu____2842) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____2854 = FStar_Options.print_universes ()  in
          if uu____2854
          then
            let uu____2855 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____2855 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____2860,uu____2861,uu____2862) ->
          let uu____2867 = FStar_Options.print_universes ()  in
          if uu____2867
          then
            let uu____2868 = univ_names_to_string univs1  in
            let uu____2869 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____2868
              lid.FStar_Ident.str uu____2869
          else
            (let uu____2871 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____2871)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____2875 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____2876 =
            let uu____2877 = FStar_Options.print_universes ()  in
            if uu____2877
            then
              let uu____2878 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____2878
            else ""  in
          let uu____2880 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____2875
            lid.FStar_Ident.str uu____2876 uu____2880
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____2884 = FStar_Options.print_universes ()  in
          if uu____2884
          then
            let uu____2885 = univ_names_to_string us  in
            let uu____2886 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____2885 uu____2886
          else
            (let uu____2888 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2888)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____2890) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____2896 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____2896
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2898) ->
          let uu____2907 =
            let uu____2908 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____2908 (FStar_String.concat "\n")  in
          Prims.strcat "(* Sig_bundle *)" uu____2907
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____2944) -> lift_wp
            | (uu____2951,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____2959 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____2959 with
           | (us,t) ->
               let uu____2970 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____2971 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____2972 = univ_names_to_string us  in
               let uu____2973 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2970
                 uu____2971 uu____2972 uu____2973)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
          let uu____2983 = FStar_Options.print_universes ()  in
          if uu____2983
          then
            let uu____2984 =
              let uu____2989 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____2989  in
            (match uu____2984 with
             | (univs2,t) ->
                 let uu____3002 =
                   let uu____3007 =
                     let uu____3008 = FStar_Syntax_Subst.compress t  in
                     uu____3008.FStar_Syntax_Syntax.n  in
                   match uu____3007 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____3037 -> failwith "impossible"  in
                 (match uu____3002 with
                  | (tps1,c1) ->
                      let uu____3044 = sli l  in
                      let uu____3045 = univ_names_to_string univs2  in
                      let uu____3046 = binders_to_string " " tps1  in
                      let uu____3047 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____3044
                        uu____3045 uu____3046 uu____3047))
          else
            (let uu____3049 = sli l  in
             let uu____3050 = binders_to_string " " tps  in
             let uu____3051 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____3049 uu____3050
               uu____3051)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____3058 =
            let uu____3059 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____3059  in
          let uu____3064 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____3058 uu____3064
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____3065 ->
        let uu____3068 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.strcat uu____3068 (Prims.strcat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3079 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3079 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3085,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3087;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3089;
                       FStar_Syntax_Syntax.lbdef = uu____3090;
                       FStar_Syntax_Syntax.lbattrs = uu____3091;
                       FStar_Syntax_Syntax.lbpos = uu____3092;_}::[]),uu____3093)
        ->
        let uu____3114 = lbname_to_string lb  in
        let uu____3115 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3114 uu____3115
    | uu____3116 ->
        let uu____3117 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3117 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3133 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3134 =
      let uu____3135 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3135 (FStar_String.concat "\n")  in
    let uu____3140 =
      let uu____3141 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3141 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3133 uu____3134 uu____3140
  
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
          (let uu____3175 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3175))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3182 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3182)));
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
           (let uu____3216 = f x  in
            FStar_Util.string_builder_append strb uu____3216);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3223 = f x1  in
                 FStar_Util.string_builder_append strb uu____3223)) xs;
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
           (let uu____3261 = f x  in
            FStar_Util.string_builder_append strb uu____3261);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3268 = f x1  in
                 FStar_Util.string_builder_append strb uu____3268)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3284 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3284
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___217_3295  ->
    match uu___217_3295 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____3305 =
          let uu____3306 =
            let uu____3307 =
              let uu____3308 =
                let uu____3309 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____3309 (FStar_String.concat " ")  in
              Prims.strcat uu____3308 ")"  in
            Prims.strcat " " uu____3307  in
          Prims.strcat h uu____3306  in
        Prims.strcat "(" uu____3305
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____3316 =
          let uu____3317 = emb_typ_to_string a  in
          let uu____3318 =
            let uu____3319 = emb_typ_to_string b  in
            Prims.strcat ") -> " uu____3319  in
          Prims.strcat uu____3317 uu____3318  in
        Prims.strcat "(" uu____3316
  