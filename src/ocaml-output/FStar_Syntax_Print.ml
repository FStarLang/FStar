open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___200_5  ->
    match uu___200_5 with
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
  fun uu___201_281  ->
    match uu___201_281 with
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
         (fun uu___202_347  ->
            match uu___202_347 with
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
  fun uu___203_589  ->
    match uu___203_589 with
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
    let uu____674 =
      let uu____675 = FStar_Options.ugly ()  in Prims.op_Negation uu____675
       in
    if uu____674
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____679 = FStar_Syntax_Subst.compress_univ u  in
       match uu____679 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____691 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____691
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____693 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____693 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____707 = univ_to_string u2  in
                let uu____708 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____707 uu____708)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____712 =
             let uu____713 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____713 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____712
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____727 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____727 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____737 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____737 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___204_748  ->
    match uu___204_748 with
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
        let uu____750 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____750
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____753 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____753 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____764 =
          let uu____765 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____765  in
        let uu____766 =
          let uu____767 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____767 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____764 uu____766
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____786 =
          let uu____787 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____787  in
        let uu____788 =
          let uu____789 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____789 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____786 uu____788
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____799 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____799
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
    | uu____810 ->
        let uu____813 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____813 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____831 ->
        let uu____834 = quals_to_string quals  in Prims.strcat uu____834 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____978 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____978
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____980 = nm_to_string x  in Prims.strcat "Tm_name: " uu____980
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____982 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____982
    | FStar_Syntax_Syntax.Tm_uinst uu____983 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____990 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____991 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____992,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____993;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1008,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1009;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1024 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1043 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1058 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1065 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1082 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1105 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1132 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1145 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1158,m) ->
        let uu____1196 = FStar_ST.op_Bang m  in
        (match uu____1196 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1256 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1261,m) ->
        let uu____1267 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1267
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1268 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1270 =
      let uu____1271 = FStar_Options.ugly ()  in Prims.op_Negation uu____1271
       in
    if uu____1270
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1279 = FStar_Options.print_implicits ()  in
         if uu____1279 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1283 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1306,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1330 =
             let uu____1331 =
               let uu____1340 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1340  in
             uu____1331 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1330
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1395;_})
           ->
           let uu____1410 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1410
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1412;_})
           ->
           let uu____1427 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1427
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1447 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1481 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1503  ->
                                 match uu____1503 with
                                 | (t1,uu____1511) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1481
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1447 (FStar_String.concat "\\/")  in
           let uu____1520 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1520
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1532 = tag_of_term t  in
           let uu____1533 = sli m  in
           let uu____1534 = term_to_string t'  in
           let uu____1535 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1532 uu____1533
             uu____1534 uu____1535
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1548 = tag_of_term t  in
           let uu____1549 = term_to_string t'  in
           let uu____1550 = sli m0  in
           let uu____1551 = sli m1  in
           let uu____1552 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1548
             uu____1549 uu____1550 uu____1551 uu____1552
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1561 = FStar_Range.string_of_range r  in
           let uu____1562 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1561
             uu____1562
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1569 = lid_to_string l  in
           let uu____1570 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1571 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1569 uu____1570
             uu____1571
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1573) ->
           let uu____1578 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1578
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1580 = db_to_string x3  in
           let uu____1581 =
             let uu____1582 =
               let uu____1583 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1583 ")"  in
             Prims.strcat ":(" uu____1582  in
           Prims.strcat uu____1580 uu____1581
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1587)) ->
           let uu____1602 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1602
           then ctx_uvar_to_string u
           else
             (let uu____1604 =
                let uu____1605 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1605  in
              Prims.strcat "?" uu____1604)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1624 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1624
           then
             let uu____1625 = ctx_uvar_to_string u  in
             let uu____1626 =
               let uu____1627 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1627 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1625 uu____1626
           else
             (let uu____1639 =
                let uu____1640 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1640  in
              Prims.strcat "?" uu____1639)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1643 = FStar_Options.print_universes ()  in
           if uu____1643
           then
             let uu____1644 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1644
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1668 = binders_to_string " -> " bs  in
           let uu____1669 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1668 uu____1669
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1698 = binders_to_string " " bs  in
                let uu____1699 = term_to_string t2  in
                let uu____1700 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1704 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1704)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1698 uu____1699
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1700
            | uu____1707 ->
                let uu____1710 = binders_to_string " " bs  in
                let uu____1711 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1710 uu____1711)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1718 = bv_to_string xt  in
           let uu____1719 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1720 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1718 uu____1719 uu____1720
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1749 = term_to_string t  in
           let uu____1750 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1749 uu____1750
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1769 = lbs_to_string [] lbs  in
           let uu____1770 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1769 uu____1770
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1831 =
                   let uu____1832 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1832
                     (FStar_Util.dflt "default")
                    in
                 let uu____1837 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1831 uu____1837
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1853 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1853
              in
           let uu____1854 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1854 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1893 = term_to_string head1  in
           let uu____1894 =
             let uu____1895 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1925  ->
                       match uu____1925 with
                       | (p,wopt,e) ->
                           let uu____1941 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1942 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1944 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1944
                              in
                           let uu____1945 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1941
                             uu____1942 uu____1945))
                in
             FStar_Util.concat_l "\n\t|" uu____1895  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1893 uu____1894
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1952 = FStar_Options.print_universes ()  in
           if uu____1952
           then
             let uu____1953 = term_to_string t  in
             let uu____1954 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1953 uu____1954
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1957 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1958 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1959 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1957 uu____1958
      uu____1959

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___205_1960  ->
    match uu___205_1960 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1963 = FStar_Util.string_of_int i  in
        let uu____1964 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1963 uu____1964
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1967 = bv_to_string x  in
        let uu____1968 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1967 uu____1968
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1975 = bv_to_string x  in
        let uu____1976 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____1975 uu____1976
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1979 = FStar_Util.string_of_int i  in
        let uu____1980 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1979 uu____1980
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1983 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1983

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1985 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1985 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1995 =
      let uu____1996 = FStar_Options.ugly ()  in Prims.op_Negation uu____1996
       in
    if uu____1995
    then
      let e =
        let uu____1998 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1998  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2021 = fv_to_string l  in
           let uu____2022 =
             let uu____2023 =
               FStar_List.map
                 (fun uu____2034  ->
                    match uu____2034 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2023 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2021 uu____2022
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2046) ->
           let uu____2051 = FStar_Options.print_bound_var_types ()  in
           if uu____2051
           then
             let uu____2052 = bv_to_string x1  in
             let uu____2053 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2052 uu____2053
           else
             (let uu____2055 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2055)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2057 = FStar_Options.print_bound_var_types ()  in
           if uu____2057
           then
             let uu____2058 = bv_to_string x1  in
             let uu____2059 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2058 uu____2059
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2063 = FStar_Options.print_real_names ()  in
           if uu____2063
           then
             let uu____2064 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2064
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2076 = quals_to_string' quals  in
      let uu____2077 =
        let uu____2078 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2094 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2095 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2096 =
                    let uu____2097 = FStar_Options.print_universes ()  in
                    if uu____2097
                    then
                      let uu____2098 =
                        let uu____2099 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2099 ">"  in
                      Prims.strcat "<" uu____2098
                    else ""  in
                  let uu____2101 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2102 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2094
                    uu____2095 uu____2096 uu____2101 uu____2102))
           in
        FStar_Util.concat_l "\n and " uu____2078  in
      FStar_Util.format3 "%slet %s %s" uu____2076
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2077

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___206_2106  ->
    match uu___206_2106 with
    | [] -> ""
    | tms ->
        let uu____2112 =
          let uu____2113 =
            FStar_List.map
              (fun t  ->
                 let uu____2119 = term_to_string t  in paren uu____2119) tms
             in
          FStar_All.pipe_right uu____2113 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2112

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2123 = FStar_Options.print_effect_args ()  in
    if uu____2123
    then
      let uu____2124 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2124
    else
      (let uu____2126 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2127 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2126 uu____2127)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___207_2128  ->
    match uu___207_2128 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2129 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2132 = aqual_to_string aq  in Prims.strcat uu____2132 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2141 =
        let uu____2142 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2142  in
      if uu____2141
      then
        let uu____2143 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2143 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2149 = b  in
         match uu____2149 with
         | (a,imp) ->
             let uu____2162 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2162
             then
               let uu____2163 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2163
             else
               (let uu____2165 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2167 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2167)
                   in
                if uu____2165
                then
                  let uu____2168 = nm_to_string a  in
                  imp_to_string uu____2168 imp
                else
                  (let uu____2170 =
                     let uu____2171 = nm_to_string a  in
                     let uu____2172 =
                       let uu____2173 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2173  in
                     Prims.strcat uu____2171 uu____2172  in
                   imp_to_string uu____2170 imp)))

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
        let uu____2187 = FStar_Options.print_implicits ()  in
        if uu____2187 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2191 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2191 (FStar_String.concat sep)
      else
        (let uu____2213 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2213 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___208_2222  ->
    match uu___208_2222 with
    | (a,imp) ->
        let uu____2229 = term_to_string a  in imp_to_string uu____2229 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2238 = FStar_Options.print_implicits ()  in
      if uu____2238 then args else filter_imp args  in
    let uu____2248 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2248 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2267 = FStar_Options.ugly ()  in
      if uu____2267
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2272 =
      let uu____2273 = FStar_Options.ugly ()  in Prims.op_Negation uu____2273
       in
    if uu____2272
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2287 =
             let uu____2288 = FStar_Syntax_Subst.compress t  in
             uu____2288.FStar_Syntax_Syntax.n  in
           (match uu____2287 with
            | FStar_Syntax_Syntax.Tm_type uu____2291 when
                let uu____2292 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2292 -> term_to_string t
            | uu____2293 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2295 = univ_to_string u  in
                     let uu____2296 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2295 uu____2296
                 | uu____2297 ->
                     let uu____2300 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2300))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2311 =
             let uu____2312 = FStar_Syntax_Subst.compress t  in
             uu____2312.FStar_Syntax_Syntax.n  in
           (match uu____2311 with
            | FStar_Syntax_Syntax.Tm_type uu____2315 when
                let uu____2316 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2316 -> term_to_string t
            | uu____2317 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2319 = univ_to_string u  in
                     let uu____2320 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2319 uu____2320
                 | uu____2321 ->
                     let uu____2324 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2324))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2327 = FStar_Options.print_effect_args ()  in
             if uu____2327
             then
               let uu____2328 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2329 =
                 let uu____2330 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2330 (FStar_String.concat ", ")
                  in
               let uu____2339 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2340 =
                 let uu____2341 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2341 (FStar_String.concat ", ")
                  in
               let uu____2358 =
                 let uu____2359 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2359 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2328
                 uu____2329 uu____2339 uu____2340 uu____2358
             else
               (let uu____2369 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___209_2373  ->
                           match uu___209_2373 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2374 -> false)))
                    &&
                    (let uu____2376 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2376)
                   in
                if uu____2369
                then
                  let uu____2377 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2377
                else
                  (let uu____2379 =
                     ((let uu____2382 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2382) &&
                        (let uu____2384 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2384))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2379
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2386 =
                        (let uu____2389 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2389) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___210_2393  ->
                                   match uu___210_2393 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2394 -> false)))
                         in
                      if uu____2386
                      then
                        let uu____2395 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2395
                      else
                        (let uu____2397 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2398 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2397 uu____2398))))
              in
           let dec =
             let uu____2400 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___211_2410  ->
                       match uu___211_2410 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2416 =
                             let uu____2417 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2417
                              in
                           [uu____2416]
                       | uu____2418 -> []))
                in
             FStar_All.pipe_right uu____2400 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2422 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___212_2428  ->
    match uu___212_2428 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2443 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2477 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2499  ->
                              match uu____2499 with
                              | (t,uu____2507) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2477
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2443 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2517 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2517
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2520) ->
        let uu____2521 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2521
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2529 = sli m  in
        let uu____2530 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2529 uu____2530
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2538 = sli m  in
        let uu____2539 = sli m'  in
        let uu____2540 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2538
          uu____2539 uu____2540

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2551 = FStar_Options.ugly ()  in
      if uu____2551
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
      let uu____2565 = b  in
      match uu____2565 with
      | (a,imp) ->
          let n1 =
            let uu____2573 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2573
            then FStar_Util.JsonNull
            else
              (let uu____2575 =
                 let uu____2576 = nm_to_string a  in
                 imp_to_string uu____2576 imp  in
               FStar_Util.JsonStr uu____2575)
             in
          let t =
            let uu____2578 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2578  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2601 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2601
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2615 = FStar_Options.print_universes ()  in
    if uu____2615 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2622 =
      let uu____2623 = FStar_Options.ugly ()  in Prims.op_Negation uu____2623
       in
    if uu____2622
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2627 = s  in
       match uu____2627 with
       | (us,t) ->
           let uu____2638 =
             let uu____2639 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2639  in
           let uu____2640 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2638 uu____2640)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2646 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2647 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2648 =
      let uu____2649 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2649  in
    let uu____2650 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2651 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2646 uu____2647 uu____2648
      uu____2650 uu____2651
  
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
          let uu____2676 =
            let uu____2677 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2677  in
          if uu____2676
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2691 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2691 (FStar_String.concat ",\n\t")
                in
             let uu____2700 =
               let uu____2703 =
                 let uu____2706 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2707 =
                   let uu____2710 =
                     let uu____2711 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2711  in
                   let uu____2712 =
                     let uu____2715 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2716 =
                       let uu____2719 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2720 =
                         let uu____2723 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2724 =
                           let uu____2727 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2728 =
                             let uu____2731 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2732 =
                               let uu____2735 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2736 =
                                 let uu____2739 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2740 =
                                   let uu____2743 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2744 =
                                     let uu____2747 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2748 =
                                       let uu____2751 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2752 =
                                         let uu____2755 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2756 =
                                           let uu____2759 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2760 =
                                             let uu____2763 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2764 =
                                               let uu____2767 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2768 =
                                                 let uu____2771 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2772 =
                                                   let uu____2775 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2775]  in
                                                 uu____2771 :: uu____2772  in
                                               uu____2767 :: uu____2768  in
                                             uu____2763 :: uu____2764  in
                                           uu____2759 :: uu____2760  in
                                         uu____2755 :: uu____2756  in
                                       uu____2751 :: uu____2752  in
                                     uu____2747 :: uu____2748  in
                                   uu____2743 :: uu____2744  in
                                 uu____2739 :: uu____2740  in
                               uu____2735 :: uu____2736  in
                             uu____2731 :: uu____2732  in
                           uu____2727 :: uu____2728  in
                         uu____2723 :: uu____2724  in
                       uu____2719 :: uu____2720  in
                     uu____2715 :: uu____2716  in
                   uu____2710 :: uu____2712  in
                 uu____2706 :: uu____2707  in
               (if for_free then "_for_free " else "") :: uu____2703  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2700)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2792 =
      let uu____2793 = FStar_Options.ugly ()  in Prims.op_Negation uu____2793
       in
    if uu____2792
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2799 -> ""
    else
      (let basic =
         match x.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
             "#light \"off\""
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
             (FStar_Pervasives_Native.None )) -> "#reset-options"
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
             (FStar_Pervasives_Native.Some s)) ->
             FStar_Util.format1 "#reset-options \"%s\"" s
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s)
             -> FStar_Util.format1 "#set-options \"%s\"" s
         | FStar_Syntax_Syntax.Sig_inductive_typ
             (lid,univs1,tps,k,uu____2810,uu____2811) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2823 = FStar_Options.print_universes ()  in
             if uu____2823
             then
               let uu____2824 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2824 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2829,uu____2830,uu____2831) ->
             let uu____2836 = FStar_Options.print_universes ()  in
             if uu____2836
             then
               let uu____2837 = univ_names_to_string univs1  in
               let uu____2838 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2837
                 lid.FStar_Ident.str uu____2838
             else
               (let uu____2840 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2840)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2844 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2845 =
               let uu____2846 = FStar_Options.print_universes ()  in
               if uu____2846
               then
                 let uu____2847 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2847
               else ""  in
             let uu____2849 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2844
               lid.FStar_Ident.str uu____2845 uu____2849
         | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
             let uu____2853 = FStar_Options.print_universes ()  in
             if uu____2853
             then
               let uu____2854 = univ_names_to_string us  in
               let uu____2855 = term_to_string f  in
               FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
                 uu____2854 uu____2855
             else
               (let uu____2857 = term_to_string f  in
                FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str
                  uu____2857)
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2859) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2865 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2865
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2867) ->
             let uu____2876 =
               let uu____2877 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2877 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2876
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
               | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None
                  ) -> failwith "impossible"
               | (FStar_Pervasives_Native.Some lift_wp,uu____2913) -> lift_wp
               | (uu____2920,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2928 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2928 with
              | (us,t) ->
                  let uu____2939 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2940 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2941 = univ_names_to_string us  in
                  let uu____2942 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2939 uu____2940 uu____2941 uu____2942)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2952 = FStar_Options.print_universes ()  in
             if uu____2952
             then
               let uu____2953 =
                 let uu____2958 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2958  in
               (match uu____2953 with
                | (univs2,t) ->
                    let uu____2971 =
                      let uu____2976 =
                        let uu____2977 = FStar_Syntax_Subst.compress t  in
                        uu____2977.FStar_Syntax_Syntax.n  in
                      match uu____2976 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____3006 -> failwith "impossible"  in
                    (match uu____2971 with
                     | (tps1,c1) ->
                         let uu____3013 = sli l  in
                         let uu____3014 = univ_names_to_string univs2  in
                         let uu____3015 = binders_to_string " " tps1  in
                         let uu____3016 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____3013 uu____3014 uu____3015 uu____3016))
             else
               (let uu____3018 = sli l  in
                let uu____3019 = binders_to_string " " tps  in
                let uu____3020 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____3018 uu____3019
                  uu____3020)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____3027 =
               let uu____3028 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____3028  in
             let uu____3033 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____3027 uu____3033
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____3034 ->
           let uu____3037 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____3037 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3048 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3048 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3054,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3056;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3058;
                       FStar_Syntax_Syntax.lbdef = uu____3059;
                       FStar_Syntax_Syntax.lbattrs = uu____3060;
                       FStar_Syntax_Syntax.lbpos = uu____3061;_}::[]),uu____3062)
        ->
        let uu____3083 = lbname_to_string lb  in
        let uu____3084 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3083 uu____3084
    | uu____3085 ->
        let uu____3086 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3086 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3102 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3103 =
      let uu____3104 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3104 (FStar_String.concat "\n")  in
    let uu____3109 =
      let uu____3110 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3110 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3102 uu____3103 uu____3109
  
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
          (let uu____3144 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3144))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3151 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3151)));
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
           (let uu____3185 = f x  in
            FStar_Util.string_builder_append strb uu____3185);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3192 = f x1  in
                 FStar_Util.string_builder_append strb uu____3192)) xs;
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
           (let uu____3230 = f x  in
            FStar_Util.string_builder_append strb uu____3230);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3237 = f x1  in
                 FStar_Util.string_builder_append strb uu____3237)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3253 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3253
  