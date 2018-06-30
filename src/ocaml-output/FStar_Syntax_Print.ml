open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___201_5  ->
    match uu___201_5 with
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
  fun uu___202_281  ->
    match uu___202_281 with
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
         (fun uu___203_347  ->
            match uu___203_347 with
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
  fun uu___204_589  ->
    match uu___204_589 with
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
  fun uu___205_740  ->
    match uu___205_740 with
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
        (uu____1000,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1001;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1016 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1035 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1050 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1057 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1074 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1097 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1124 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1137 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1150,m) ->
        let uu____1188 = FStar_ST.op_Bang m  in
        (match uu____1188 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1244 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1249,m) ->
        let uu____1255 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1255
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1256 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1258 =
      let uu____1259 = FStar_Options.ugly ()  in Prims.op_Negation uu____1259
       in
    if uu____1258
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1267 = FStar_Options.print_implicits ()  in
         if uu____1267 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1271 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1294,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1318 =
             let uu____1319 =
               let uu____1320 =
                 let uu____1321 =
                   let uu____1330 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1330  in
                 uu____1321 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1320  in
             Prims.strcat uu____1319 "]"  in
           Prims.strcat "[lazy:" uu____1318
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1381;_})
           ->
           let uu____1396 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1396
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1398;_})
           ->
           let uu____1413 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1413
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1433 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1467 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1489  ->
                                 match uu____1489 with
                                 | (t1,uu____1497) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1467
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1433 (FStar_String.concat "\\/")  in
           let uu____1506 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1506
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1518 = tag_of_term t  in
           let uu____1519 = sli m  in
           let uu____1520 = term_to_string t'  in
           let uu____1521 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1518 uu____1519
             uu____1520 uu____1521
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1534 = tag_of_term t  in
           let uu____1535 = term_to_string t'  in
           let uu____1536 = sli m0  in
           let uu____1537 = sli m1  in
           let uu____1538 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1534
             uu____1535 uu____1536 uu____1537 uu____1538
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1547 = FStar_Range.string_of_range r  in
           let uu____1548 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1547
             uu____1548
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1555 = lid_to_string l  in
           let uu____1556 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1557 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1555 uu____1556
             uu____1557
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1559) ->
           let uu____1564 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1564
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1566 = db_to_string x3  in
           let uu____1567 =
             let uu____1568 =
               let uu____1569 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1569 ")"  in
             Prims.strcat ":(" uu____1568  in
           Prims.strcat uu____1566 uu____1567
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1573)) ->
           let uu____1588 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1588
           then ctx_uvar_to_string u
           else
             (let uu____1590 =
                let uu____1591 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1591  in
              Prims.strcat "?" uu____1590)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1610 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1610
           then
             let uu____1611 = ctx_uvar_to_string u  in
             let uu____1612 =
               let uu____1613 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1613 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1611 uu____1612
           else
             (let uu____1625 =
                let uu____1626 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1626  in
              Prims.strcat "?" uu____1625)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1629 = FStar_Options.print_universes ()  in
           if uu____1629
           then
             let uu____1630 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1630
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1654 = binders_to_string " -> " bs  in
           let uu____1655 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1654 uu____1655
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1684 = binders_to_string " " bs  in
                let uu____1685 = term_to_string t2  in
                let uu____1686 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1690 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1690)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1684 uu____1685
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1686
            | uu____1693 ->
                let uu____1696 = binders_to_string " " bs  in
                let uu____1697 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1696 uu____1697)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1704 = bv_to_string xt  in
           let uu____1705 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1706 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1704 uu____1705 uu____1706
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1735 = term_to_string t  in
           let uu____1736 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1735 uu____1736
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1755 = lbs_to_string [] lbs  in
           let uu____1756 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1755 uu____1756
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1817 =
                   let uu____1818 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1818
                     (FStar_Util.dflt "default")
                    in
                 let uu____1823 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1817 uu____1823
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1839 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1839
              in
           let uu____1840 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1840 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1879 = term_to_string head1  in
           let uu____1880 =
             let uu____1881 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1911  ->
                       match uu____1911 with
                       | (p,wopt,e) ->
                           let uu____1927 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1928 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1930 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1930
                              in
                           let uu____1931 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1927
                             uu____1928 uu____1931))
                in
             FStar_Util.concat_l "\n\t|" uu____1881  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1879 uu____1880
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1938 = FStar_Options.print_universes ()  in
           if uu____1938
           then
             let uu____1939 = term_to_string t  in
             let uu____1940 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1939 uu____1940
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1943 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1944 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1945 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1943 uu____1944
      uu____1945

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___206_1946  ->
    match uu___206_1946 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1949 = FStar_Util.string_of_int i  in
        let uu____1950 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1949 uu____1950
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1953 = bv_to_string x  in
        let uu____1954 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1953 uu____1954
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1961 = bv_to_string x  in
        let uu____1962 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____1961 uu____1962
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1965 = FStar_Util.string_of_int i  in
        let uu____1966 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1965 uu____1966
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1969 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1969

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1971 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1971 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1981 =
      let uu____1982 = FStar_Options.ugly ()  in Prims.op_Negation uu____1982
       in
    if uu____1981
    then
      let e =
        let uu____1984 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1984  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2007 = fv_to_string l  in
           let uu____2008 =
             let uu____2009 =
               FStar_List.map
                 (fun uu____2020  ->
                    match uu____2020 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2009 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2007 uu____2008
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2032) ->
           let uu____2037 = FStar_Options.print_bound_var_types ()  in
           if uu____2037
           then
             let uu____2038 = bv_to_string x1  in
             let uu____2039 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2038 uu____2039
           else
             (let uu____2041 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2041)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2043 = FStar_Options.print_bound_var_types ()  in
           if uu____2043
           then
             let uu____2044 = bv_to_string x1  in
             let uu____2045 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2044 uu____2045
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2049 = FStar_Options.print_real_names ()  in
           if uu____2049
           then
             let uu____2050 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2050
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2062 = quals_to_string' quals  in
      let uu____2063 =
        let uu____2064 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2080 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2081 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2082 =
                    let uu____2083 = FStar_Options.print_universes ()  in
                    if uu____2083
                    then
                      let uu____2084 =
                        let uu____2085 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2085 ">"  in
                      Prims.strcat "<" uu____2084
                    else ""  in
                  let uu____2087 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2088 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2080
                    uu____2081 uu____2082 uu____2087 uu____2088))
           in
        FStar_Util.concat_l "\n and " uu____2064  in
      FStar_Util.format3 "%slet %s %s" uu____2062
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2063

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___207_2092  ->
    match uu___207_2092 with
    | [] -> ""
    | tms ->
        let uu____2098 =
          let uu____2099 =
            FStar_List.map
              (fun t  ->
                 let uu____2105 = term_to_string t  in paren uu____2105) tms
             in
          FStar_All.pipe_right uu____2099 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2098

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2109 = FStar_Options.print_effect_args ()  in
    if uu____2109
    then
      let uu____2110 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2110
    else
      (let uu____2112 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2113 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2112 uu____2113)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___208_2114  ->
    match uu___208_2114 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2115 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2118 = aqual_to_string aq  in Prims.strcat uu____2118 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2127 =
        let uu____2128 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2128  in
      if uu____2127
      then
        let uu____2129 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2129 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2135 = b  in
         match uu____2135 with
         | (a,imp) ->
             let uu____2148 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2148
             then
               let uu____2149 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2149
             else
               (let uu____2151 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2153 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2153)
                   in
                if uu____2151
                then
                  let uu____2154 = nm_to_string a  in
                  imp_to_string uu____2154 imp
                else
                  (let uu____2156 =
                     let uu____2157 = nm_to_string a  in
                     let uu____2158 =
                       let uu____2159 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2159  in
                     Prims.strcat uu____2157 uu____2158  in
                   imp_to_string uu____2156 imp)))

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
        let uu____2173 = FStar_Options.print_implicits ()  in
        if uu____2173 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2177 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2177 (FStar_String.concat sep)
      else
        (let uu____2199 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2199 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___209_2208  ->
    match uu___209_2208 with
    | (a,imp) ->
        let uu____2215 = term_to_string a  in imp_to_string uu____2215 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2224 = FStar_Options.print_implicits ()  in
      if uu____2224 then args else filter_imp args  in
    let uu____2234 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2234 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2253 = FStar_Options.ugly ()  in
      if uu____2253
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2258 =
      let uu____2259 = FStar_Options.ugly ()  in Prims.op_Negation uu____2259
       in
    if uu____2258
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2273 =
             let uu____2274 = FStar_Syntax_Subst.compress t  in
             uu____2274.FStar_Syntax_Syntax.n  in
           (match uu____2273 with
            | FStar_Syntax_Syntax.Tm_type uu____2277 when
                let uu____2278 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2278 -> term_to_string t
            | uu____2279 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2281 = univ_to_string u  in
                     let uu____2282 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2281 uu____2282
                 | uu____2283 ->
                     let uu____2286 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2286))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2297 =
             let uu____2298 = FStar_Syntax_Subst.compress t  in
             uu____2298.FStar_Syntax_Syntax.n  in
           (match uu____2297 with
            | FStar_Syntax_Syntax.Tm_type uu____2301 when
                let uu____2302 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2302 -> term_to_string t
            | uu____2303 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2305 = univ_to_string u  in
                     let uu____2306 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2305 uu____2306
                 | uu____2307 ->
                     let uu____2310 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2310))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2313 = FStar_Options.print_effect_args ()  in
             if uu____2313
             then
               let uu____2314 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2315 =
                 let uu____2316 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2316 (FStar_String.concat ", ")
                  in
               let uu____2325 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2326 =
                 let uu____2327 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2327 (FStar_String.concat ", ")
                  in
               let uu____2344 =
                 let uu____2345 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2345 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2314
                 uu____2315 uu____2325 uu____2326 uu____2344
             else
               (let uu____2355 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_2359  ->
                           match uu___210_2359 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2360 -> false)))
                    &&
                    (let uu____2362 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2362)
                   in
                if uu____2355
                then
                  let uu____2363 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2363
                else
                  (let uu____2365 =
                     ((let uu____2368 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2368) &&
                        (let uu____2370 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2370))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2365
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2372 =
                        (let uu____2375 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2375) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2379  ->
                                   match uu___211_2379 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2380 -> false)))
                         in
                      if uu____2372
                      then
                        let uu____2381 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2381
                      else
                        (let uu____2383 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2384 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2383 uu____2384))))
              in
           let dec =
             let uu____2386 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2396  ->
                       match uu___212_2396 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2402 =
                             let uu____2403 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2403
                              in
                           [uu____2402]
                       | uu____2404 -> []))
                in
             FStar_All.pipe_right uu____2386 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2408 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___213_2414  ->
    match uu___213_2414 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2429 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2463 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2485  ->
                              match uu____2485 with
                              | (t,uu____2493) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2463
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2429 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2503 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2503
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2506) ->
        let uu____2507 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2507
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2515 = sli m  in
        let uu____2516 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2515 uu____2516
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2524 = sli m  in
        let uu____2525 = sli m'  in
        let uu____2526 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2524
          uu____2525 uu____2526

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2537 = FStar_Options.ugly ()  in
      if uu____2537
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
      let uu____2551 = b  in
      match uu____2551 with
      | (a,imp) ->
          let n1 =
            let uu____2559 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2559
            then FStar_Util.JsonNull
            else
              (let uu____2561 =
                 let uu____2562 = nm_to_string a  in
                 imp_to_string uu____2562 imp  in
               FStar_Util.JsonStr uu____2561)
             in
          let t =
            let uu____2564 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2564  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2587 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2587
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2601 = FStar_Options.print_universes ()  in
    if uu____2601 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2608 =
      let uu____2609 = FStar_Options.ugly ()  in Prims.op_Negation uu____2609
       in
    if uu____2608
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2613 = s  in
       match uu____2613 with
       | (us,t) ->
           let uu____2624 =
             let uu____2625 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2625  in
           let uu____2626 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2624 uu____2626)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2632 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2633 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2634 =
      let uu____2635 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2635  in
    let uu____2636 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2637 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2632 uu____2633 uu____2634
      uu____2636 uu____2637
  
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
          let uu____2662 =
            let uu____2663 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2663  in
          if uu____2662
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2677 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2677 (FStar_String.concat ",\n\t")
                in
             let uu____2686 =
               let uu____2689 =
                 let uu____2692 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2693 =
                   let uu____2696 =
                     let uu____2697 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2697  in
                   let uu____2698 =
                     let uu____2701 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2702 =
                       let uu____2705 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2706 =
                         let uu____2709 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2710 =
                           let uu____2713 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2714 =
                             let uu____2717 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2718 =
                               let uu____2721 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2722 =
                                 let uu____2725 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2726 =
                                   let uu____2729 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2730 =
                                     let uu____2733 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2734 =
                                       let uu____2737 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2738 =
                                         let uu____2741 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2742 =
                                           let uu____2745 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2746 =
                                             let uu____2749 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2750 =
                                               let uu____2753 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2754 =
                                                 let uu____2757 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2758 =
                                                   let uu____2761 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2761]  in
                                                 uu____2757 :: uu____2758  in
                                               uu____2753 :: uu____2754  in
                                             uu____2749 :: uu____2750  in
                                           uu____2745 :: uu____2746  in
                                         uu____2741 :: uu____2742  in
                                       uu____2737 :: uu____2738  in
                                     uu____2733 :: uu____2734  in
                                   uu____2729 :: uu____2730  in
                                 uu____2725 :: uu____2726  in
                               uu____2721 :: uu____2722  in
                             uu____2717 :: uu____2718  in
                           uu____2713 :: uu____2714  in
                         uu____2709 :: uu____2710  in
                       uu____2705 :: uu____2706  in
                     uu____2701 :: uu____2702  in
                   uu____2696 :: uu____2698  in
                 uu____2692 :: uu____2693  in
               (if for_free then "_for_free " else "") :: uu____2689  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2686)
  
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
          (lid,univs1,tps,k,uu____2786,uu____2787) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____2799 = FStar_Options.print_universes ()  in
          if uu____2799
          then
            let uu____2800 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____2800 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____2805,uu____2806,uu____2807) ->
          let uu____2812 = FStar_Options.print_universes ()  in
          if uu____2812
          then
            let uu____2813 = univ_names_to_string univs1  in
            let uu____2814 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____2813
              lid.FStar_Ident.str uu____2814
          else
            (let uu____2816 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____2816)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____2820 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____2821 =
            let uu____2822 = FStar_Options.print_universes ()  in
            if uu____2822
            then
              let uu____2823 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____2823
            else ""  in
          let uu____2825 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____2820
            lid.FStar_Ident.str uu____2821 uu____2825
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____2829 = FStar_Options.print_universes ()  in
          if uu____2829
          then
            let uu____2830 = univ_names_to_string us  in
            let uu____2831 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____2830 uu____2831
          else
            (let uu____2833 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2833)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____2835) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____2841 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____2841
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2843) ->
          let uu____2852 =
            let uu____2853 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____2853 (FStar_String.concat "\n")  in
          Prims.strcat "(* Sig_bundle *)" uu____2852
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____2889) -> lift_wp
            | (uu____2896,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____2904 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____2904 with
           | (us,t) ->
               let uu____2915 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____2916 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____2917 = univ_names_to_string us  in
               let uu____2918 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2915
                 uu____2916 uu____2917 uu____2918)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
          let uu____2928 = FStar_Options.print_universes ()  in
          if uu____2928
          then
            let uu____2929 =
              let uu____2934 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____2934  in
            (match uu____2929 with
             | (univs2,t) ->
                 let uu____2947 =
                   let uu____2952 =
                     let uu____2953 = FStar_Syntax_Subst.compress t  in
                     uu____2953.FStar_Syntax_Syntax.n  in
                   match uu____2952 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____2982 -> failwith "impossible"  in
                 (match uu____2947 with
                  | (tps1,c1) ->
                      let uu____2989 = sli l  in
                      let uu____2990 = univ_names_to_string univs2  in
                      let uu____2991 = binders_to_string " " tps1  in
                      let uu____2992 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____2989
                        uu____2990 uu____2991 uu____2992))
          else
            (let uu____2994 = sli l  in
             let uu____2995 = binders_to_string " " tps  in
             let uu____2996 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____2994 uu____2995
               uu____2996)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____3003 =
            let uu____3004 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____3004  in
          let uu____3009 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____3003 uu____3009
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____3010 ->
        let uu____3013 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.strcat uu____3013 (Prims.strcat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3024 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3024 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3030,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3032;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3034;
                       FStar_Syntax_Syntax.lbdef = uu____3035;
                       FStar_Syntax_Syntax.lbattrs = uu____3036;
                       FStar_Syntax_Syntax.lbpos = uu____3037;_}::[]),uu____3038)
        ->
        let uu____3059 = lbname_to_string lb  in
        let uu____3060 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3059 uu____3060
    | uu____3061 ->
        let uu____3062 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3062 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3078 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3079 =
      let uu____3080 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3080 (FStar_String.concat "\n")  in
    let uu____3085 =
      let uu____3086 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3086 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3078 uu____3079 uu____3085
  
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
          (let uu____3120 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3120))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3127 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3127)));
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
           (let uu____3161 = f x  in
            FStar_Util.string_builder_append strb uu____3161);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3168 = f x1  in
                 FStar_Util.string_builder_append strb uu____3168)) xs;
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
           (let uu____3206 = f x  in
            FStar_Util.string_builder_append strb uu____3206);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3213 = f x1  in
                 FStar_Util.string_builder_append strb uu____3213)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3229 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3229
  