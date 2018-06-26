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
  fun uu___205_748  ->
    match uu___205_748 with
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
         | FStar_Pervasives_Native.Some uu____1252 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1257,m) ->
        let uu____1263 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1263
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1264 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1266 =
      let uu____1267 = FStar_Options.ugly ()  in Prims.op_Negation uu____1267
       in
    if uu____1266
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1275 = FStar_Options.print_implicits ()  in
         if uu____1275 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1279 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1302,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1326 =
             let uu____1327 =
               let uu____1336 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1336  in
             uu____1327 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1326
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1387;_})
           ->
           let uu____1402 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1402
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1404;_})
           ->
           let uu____1419 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1419
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1439 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1473 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1495  ->
                                 match uu____1495 with
                                 | (t1,uu____1503) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1473
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1439 (FStar_String.concat "\\/")  in
           let uu____1512 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1512
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1524 = tag_of_term t  in
           let uu____1525 = sli m  in
           let uu____1526 = term_to_string t'  in
           let uu____1527 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1524 uu____1525
             uu____1526 uu____1527
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1540 = tag_of_term t  in
           let uu____1541 = term_to_string t'  in
           let uu____1542 = sli m0  in
           let uu____1543 = sli m1  in
           let uu____1544 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1540
             uu____1541 uu____1542 uu____1543 uu____1544
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1553 = FStar_Range.string_of_range r  in
           let uu____1554 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1553
             uu____1554
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1561 = lid_to_string l  in
           let uu____1562 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1563 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1561 uu____1562
             uu____1563
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1565) ->
           let uu____1570 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1570
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1572 = db_to_string x3  in
           let uu____1573 =
             let uu____1574 =
               let uu____1575 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1575 ")"  in
             Prims.strcat ":(" uu____1574  in
           Prims.strcat uu____1572 uu____1573
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1579)) ->
           let uu____1594 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1594
           then ctx_uvar_to_string u
           else
             (let uu____1596 =
                let uu____1597 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1597  in
              Prims.strcat "?" uu____1596)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1616 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1616
           then
             let uu____1617 = ctx_uvar_to_string u  in
             let uu____1618 =
               let uu____1619 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1619 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1617 uu____1618
           else
             (let uu____1631 =
                let uu____1632 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1632  in
              Prims.strcat "?" uu____1631)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1635 = FStar_Options.print_universes ()  in
           if uu____1635
           then
             let uu____1636 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1636
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1660 = binders_to_string " -> " bs  in
           let uu____1661 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1660 uu____1661
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1690 = binders_to_string " " bs  in
                let uu____1691 = term_to_string t2  in
                let uu____1692 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1696 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1696)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1690 uu____1691
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1692
            | uu____1699 ->
                let uu____1702 = binders_to_string " " bs  in
                let uu____1703 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1702 uu____1703)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1710 = bv_to_string xt  in
           let uu____1711 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1712 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1710 uu____1711 uu____1712
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1741 = term_to_string t  in
           let uu____1742 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1741 uu____1742
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1761 = lbs_to_string [] lbs  in
           let uu____1762 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1761 uu____1762
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1823 =
                   let uu____1824 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1824
                     (FStar_Util.dflt "default")
                    in
                 let uu____1829 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1823 uu____1829
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1845 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1845
              in
           let uu____1846 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1846 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1885 = term_to_string head1  in
           let uu____1886 =
             let uu____1887 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1917  ->
                       match uu____1917 with
                       | (p,wopt,e) ->
                           let uu____1933 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1934 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1936 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1936
                              in
                           let uu____1937 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1933
                             uu____1934 uu____1937))
                in
             FStar_Util.concat_l "\n\t|" uu____1887  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1885 uu____1886
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1944 = FStar_Options.print_universes ()  in
           if uu____1944
           then
             let uu____1945 = term_to_string t  in
             let uu____1946 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1945 uu____1946
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1949 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1950 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1951 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1949 uu____1950
      uu____1951

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___206_1952  ->
    match uu___206_1952 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1955 = FStar_Util.string_of_int i  in
        let uu____1956 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1955 uu____1956
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1959 = bv_to_string x  in
        let uu____1960 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1959 uu____1960
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1967 = bv_to_string x  in
        let uu____1968 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____1967 uu____1968
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1971 = FStar_Util.string_of_int i  in
        let uu____1972 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1971 uu____1972
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1975 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1975

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1977 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1977 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1987 =
      let uu____1988 = FStar_Options.ugly ()  in Prims.op_Negation uu____1988
       in
    if uu____1987
    then
      let e =
        let uu____1990 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1990  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2013 = fv_to_string l  in
           let uu____2014 =
             let uu____2015 =
               FStar_List.map
                 (fun uu____2026  ->
                    match uu____2026 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2015 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2013 uu____2014
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2038) ->
           let uu____2043 = FStar_Options.print_bound_var_types ()  in
           if uu____2043
           then
             let uu____2044 = bv_to_string x1  in
             let uu____2045 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2044 uu____2045
           else
             (let uu____2047 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2047)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2049 = FStar_Options.print_bound_var_types ()  in
           if uu____2049
           then
             let uu____2050 = bv_to_string x1  in
             let uu____2051 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2050 uu____2051
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2055 = FStar_Options.print_real_names ()  in
           if uu____2055
           then
             let uu____2056 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2056
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2068 = quals_to_string' quals  in
      let uu____2069 =
        let uu____2070 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2086 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2087 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2088 =
                    let uu____2089 = FStar_Options.print_universes ()  in
                    if uu____2089
                    then
                      let uu____2090 =
                        let uu____2091 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2091 ">"  in
                      Prims.strcat "<" uu____2090
                    else ""  in
                  let uu____2093 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2094 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2086
                    uu____2087 uu____2088 uu____2093 uu____2094))
           in
        FStar_Util.concat_l "\n and " uu____2070  in
      FStar_Util.format3 "%slet %s %s" uu____2068
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2069

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___207_2098  ->
    match uu___207_2098 with
    | [] -> ""
    | tms ->
        let uu____2104 =
          let uu____2105 =
            FStar_List.map
              (fun t  ->
                 let uu____2111 = term_to_string t  in paren uu____2111) tms
             in
          FStar_All.pipe_right uu____2105 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2104

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2115 = FStar_Options.print_effect_args ()  in
    if uu____2115
    then
      let uu____2116 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2116
    else
      (let uu____2118 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2119 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2118 uu____2119)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___208_2120  ->
    match uu___208_2120 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2121 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2124 = aqual_to_string aq  in Prims.strcat uu____2124 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2133 =
        let uu____2134 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2134  in
      if uu____2133
      then
        let uu____2135 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2135 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2141 = b  in
         match uu____2141 with
         | (a,imp) ->
             let uu____2154 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2154
             then
               let uu____2155 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2155
             else
               (let uu____2157 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2159 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2159)
                   in
                if uu____2157
                then
                  let uu____2160 = nm_to_string a  in
                  imp_to_string uu____2160 imp
                else
                  (let uu____2162 =
                     let uu____2163 = nm_to_string a  in
                     let uu____2164 =
                       let uu____2165 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2165  in
                     Prims.strcat uu____2163 uu____2164  in
                   imp_to_string uu____2162 imp)))

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
        let uu____2179 = FStar_Options.print_implicits ()  in
        if uu____2179 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2183 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2183 (FStar_String.concat sep)
      else
        (let uu____2205 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2205 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___209_2214  ->
    match uu___209_2214 with
    | (a,imp) ->
        let uu____2221 = term_to_string a  in imp_to_string uu____2221 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2230 = FStar_Options.print_implicits ()  in
      if uu____2230 then args else filter_imp args  in
    let uu____2240 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2240 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2259 = FStar_Options.ugly ()  in
      if uu____2259
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2264 =
      let uu____2265 = FStar_Options.ugly ()  in Prims.op_Negation uu____2265
       in
    if uu____2264
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2279 =
             let uu____2280 = FStar_Syntax_Subst.compress t  in
             uu____2280.FStar_Syntax_Syntax.n  in
           (match uu____2279 with
            | FStar_Syntax_Syntax.Tm_type uu____2283 when
                let uu____2284 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2284 -> term_to_string t
            | uu____2285 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2287 = univ_to_string u  in
                     let uu____2288 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2287 uu____2288
                 | uu____2289 ->
                     let uu____2292 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2292))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2303 =
             let uu____2304 = FStar_Syntax_Subst.compress t  in
             uu____2304.FStar_Syntax_Syntax.n  in
           (match uu____2303 with
            | FStar_Syntax_Syntax.Tm_type uu____2307 when
                let uu____2308 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2308 -> term_to_string t
            | uu____2309 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2311 = univ_to_string u  in
                     let uu____2312 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2311 uu____2312
                 | uu____2313 ->
                     let uu____2316 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2316))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2319 = FStar_Options.print_effect_args ()  in
             if uu____2319
             then
               let uu____2320 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2321 =
                 let uu____2322 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2322 (FStar_String.concat ", ")
                  in
               let uu____2331 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2332 =
                 let uu____2333 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2333 (FStar_String.concat ", ")
                  in
               let uu____2350 =
                 let uu____2351 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2351 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2320
                 uu____2321 uu____2331 uu____2332 uu____2350
             else
               (let uu____2361 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_2365  ->
                           match uu___210_2365 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2366 -> false)))
                    &&
                    (let uu____2368 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2368)
                   in
                if uu____2361
                then
                  let uu____2369 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2369
                else
                  (let uu____2371 =
                     ((let uu____2374 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2374) &&
                        (let uu____2376 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2376))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2371
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2378 =
                        (let uu____2381 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2381) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2385  ->
                                   match uu___211_2385 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2386 -> false)))
                         in
                      if uu____2378
                      then
                        let uu____2387 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2387
                      else
                        (let uu____2389 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2390 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2389 uu____2390))))
              in
           let dec =
             let uu____2392 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2402  ->
                       match uu___212_2402 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2408 =
                             let uu____2409 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2409
                              in
                           [uu____2408]
                       | uu____2410 -> []))
                in
             FStar_All.pipe_right uu____2392 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2414 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___213_2420  ->
    match uu___213_2420 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2435 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2469 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2491  ->
                              match uu____2491 with
                              | (t,uu____2499) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2469
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2435 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2509 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2509
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2512) ->
        let uu____2513 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2513
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2521 = sli m  in
        let uu____2522 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2521 uu____2522
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2530 = sli m  in
        let uu____2531 = sli m'  in
        let uu____2532 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2530
          uu____2531 uu____2532

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2543 = FStar_Options.ugly ()  in
      if uu____2543
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
      let uu____2557 = b  in
      match uu____2557 with
      | (a,imp) ->
          let n1 =
            let uu____2565 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2565
            then FStar_Util.JsonNull
            else
              (let uu____2567 =
                 let uu____2568 = nm_to_string a  in
                 imp_to_string uu____2568 imp  in
               FStar_Util.JsonStr uu____2567)
             in
          let t =
            let uu____2570 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2570  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2593 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2593
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2607 = FStar_Options.print_universes ()  in
    if uu____2607 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2614 =
      let uu____2615 = FStar_Options.ugly ()  in Prims.op_Negation uu____2615
       in
    if uu____2614
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2619 = s  in
       match uu____2619 with
       | (us,t) ->
           let uu____2630 =
             let uu____2631 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2631  in
           let uu____2632 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2630 uu____2632)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2638 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2639 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2640 =
      let uu____2641 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2641  in
    let uu____2642 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2643 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2638 uu____2639 uu____2640
      uu____2642 uu____2643
  
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
          let uu____2668 =
            let uu____2669 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2669  in
          if uu____2668
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2683 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2683 (FStar_String.concat ",\n\t")
                in
             let uu____2692 =
               let uu____2695 =
                 let uu____2698 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2699 =
                   let uu____2702 =
                     let uu____2703 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2703  in
                   let uu____2704 =
                     let uu____2707 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2708 =
                       let uu____2711 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2712 =
                         let uu____2715 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2716 =
                           let uu____2719 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2720 =
                             let uu____2723 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2724 =
                               let uu____2727 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2728 =
                                 let uu____2731 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2732 =
                                   let uu____2735 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2736 =
                                     let uu____2739 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2740 =
                                       let uu____2743 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2744 =
                                         let uu____2747 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2748 =
                                           let uu____2751 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2752 =
                                             let uu____2755 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2756 =
                                               let uu____2759 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2760 =
                                                 let uu____2763 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2764 =
                                                   let uu____2767 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2767]  in
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
                       uu____2711 :: uu____2712  in
                     uu____2707 :: uu____2708  in
                   uu____2702 :: uu____2704  in
                 uu____2698 :: uu____2699  in
               (if for_free then "_for_free " else "") :: uu____2695  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2692)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2784 =
      let uu____2785 = FStar_Options.ugly ()  in Prims.op_Negation uu____2785
       in
    if uu____2784
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2791 -> ""
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
             (lid,univs1,tps,k,uu____2802,uu____2803) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2815 = FStar_Options.print_universes ()  in
             if uu____2815
             then
               let uu____2816 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2816 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2821,uu____2822,uu____2823) ->
             let uu____2828 = FStar_Options.print_universes ()  in
             if uu____2828
             then
               let uu____2829 = univ_names_to_string univs1  in
               let uu____2830 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2829
                 lid.FStar_Ident.str uu____2830
             else
               (let uu____2832 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2832)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2836 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2837 =
               let uu____2838 = FStar_Options.print_universes ()  in
               if uu____2838
               then
                 let uu____2839 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2839
               else ""  in
             let uu____2841 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2836
               lid.FStar_Ident.str uu____2837 uu____2841
         | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
             let uu____2845 = FStar_Options.print_universes ()  in
             if uu____2845
             then
               let uu____2846 = univ_names_to_string us  in
               let uu____2847 = term_to_string f  in
               FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
                 uu____2846 uu____2847
             else
               (let uu____2849 = term_to_string f  in
                FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str
                  uu____2849)
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2851) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2857 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2857
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2859) ->
             let uu____2868 =
               let uu____2869 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2869 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2868
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2905) -> lift_wp
               | (uu____2912,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2920 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2920 with
              | (us,t) ->
                  let uu____2931 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2932 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2933 = univ_names_to_string us  in
                  let uu____2934 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2931 uu____2932 uu____2933 uu____2934)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2944 = FStar_Options.print_universes ()  in
             if uu____2944
             then
               let uu____2945 =
                 let uu____2950 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2950  in
               (match uu____2945 with
                | (univs2,t) ->
                    let uu____2963 =
                      let uu____2968 =
                        let uu____2969 = FStar_Syntax_Subst.compress t  in
                        uu____2969.FStar_Syntax_Syntax.n  in
                      match uu____2968 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2998 -> failwith "impossible"  in
                    (match uu____2963 with
                     | (tps1,c1) ->
                         let uu____3005 = sli l  in
                         let uu____3006 = univ_names_to_string univs2  in
                         let uu____3007 = binders_to_string " " tps1  in
                         let uu____3008 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____3005 uu____3006 uu____3007 uu____3008))
             else
               (let uu____3010 = sli l  in
                let uu____3011 = binders_to_string " " tps  in
                let uu____3012 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____3010 uu____3011
                  uu____3012)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____3019 =
               let uu____3020 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____3020  in
             let uu____3025 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____3019 uu____3025
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____3026 ->
           let uu____3029 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____3029 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3040 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3040 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3046,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3048;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3050;
                       FStar_Syntax_Syntax.lbdef = uu____3051;
                       FStar_Syntax_Syntax.lbattrs = uu____3052;
                       FStar_Syntax_Syntax.lbpos = uu____3053;_}::[]),uu____3054)
        ->
        let uu____3075 = lbname_to_string lb  in
        let uu____3076 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3075 uu____3076
    | uu____3077 ->
        let uu____3078 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3078 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3094 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3095 =
      let uu____3096 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3096 (FStar_String.concat "\n")  in
    let uu____3101 =
      let uu____3102 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3102 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3094 uu____3095 uu____3101
  
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
          (let uu____3136 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3136))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3143 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3143)));
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
           (let uu____3177 = f x  in
            FStar_Util.string_builder_append strb uu____3177);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3184 = f x1  in
                 FStar_Util.string_builder_append strb uu____3184)) xs;
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
           (let uu____3222 = f x  in
            FStar_Util.string_builder_append strb uu____3222);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3229 = f x1  in
                 FStar_Util.string_builder_append strb uu____3229)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3245 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3245
  