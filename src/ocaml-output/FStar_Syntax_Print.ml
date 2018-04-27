open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___68_5  ->
    match uu___68_5 with
    | FStar_Syntax_Syntax.Delta_constant  -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____7 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_defined_at_level " uu____7
    | FStar_Syntax_Syntax.Delta_equational  -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____9 =
          let uu____10 = delta_depth_to_string d  in
          Prims.strcat uu____10 ")"  in
        Prims.strcat "Delta_abstract (" uu____9
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____16 = FStar_Options.print_real_names ()  in
    if uu____16
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____33 =
      let uu____34 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____34  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____33
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____40 = FStar_Options.print_real_names ()  in
    if uu____40
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____47 =
      let uu____48 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____48  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____47
  
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
      | uu____186 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____197 -> failwith "get_lid"
  
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
type exp = FStar_Syntax_Syntax.term[@@deriving show]
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
  'Auu____269 'Auu____270 .
    ('Auu____269,'Auu____270) FStar_Util.either -> Prims.bool
  =
  fun uu___69_279  ->
    match uu___69_279 with
    | FStar_Util.Inl uu____284 -> false
    | FStar_Util.Inr uu____285 -> true
  
let filter_imp :
  'Auu____290 .
    ('Auu____290,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____290,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___70_345  ->
            match uu___70_345 with
            | (uu____352,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____353)) -> false
            | uu____356 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____372 =
      let uu____373 = FStar_Syntax_Subst.compress e  in
      uu____373.FStar_Syntax_Syntax.n  in
    match uu____372 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____430 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____430
        then
          let uu____436 =
            let uu____441 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____441  in
          (match uu____436 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____451 =
                 let uu____454 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____454 :: xs  in
               FStar_Pervasives_Native.Some uu____451
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____464 ->
        let uu____465 = is_lex_top e  in
        if uu____465
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____506 = f hd1  in if uu____506 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____530 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____530
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____554 = get_lid e  in find_lid uu____554 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____564 = get_lid e  in find_lid uu____564 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____574 = get_lid t  in find_lid uu____574 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___71_584  ->
    match uu___71_584 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____592 = FStar_Options.hide_uvar_nums ()  in
    if uu____592
    then "?"
    else
      (let uu____594 =
         let uu____595 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____595 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____594)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____601 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____602 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____601 uu____602
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
     FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun u  ->
    let uu____624 = FStar_Options.hide_uvar_nums ()  in
    if uu____624
    then "?"
    else
      (let uu____626 =
         let uu____627 =
           let uu____628 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____628 FStar_Util.string_of_int  in
         let uu____629 =
           let uu____630 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____630  in
         Prims.strcat uu____627 uu____629  in
       Prims.strcat "?" uu____626)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____651 = FStar_Syntax_Subst.compress_univ u  in
      match uu____651 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____661 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____669 =
      let uu____670 = FStar_Options.ugly ()  in Prims.op_Negation uu____670
       in
    if uu____669
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____674 = FStar_Syntax_Subst.compress_univ u  in
       match uu____674 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____686 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____686
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____688 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____688 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____702 = univ_to_string u2  in
                let uu____703 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____702 uu____703)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____707 =
             let uu____708 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____708 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____707
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____722 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____722 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____732 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____732 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___72_743  ->
    match uu___72_743 with
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
        let uu____745 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____745
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____748 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____748 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____759 =
          let uu____760 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____760  in
        let uu____761 =
          let uu____762 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____762 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____759 uu____761
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____781 =
          let uu____782 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____782  in
        let uu____783 =
          let uu____784 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____784 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____781 uu____783
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____794 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____794
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
    | uu____805 ->
        let uu____808 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____808 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____826 ->
        let uu____829 = quals_to_string quals  in Prims.strcat uu____829 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____957 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____957
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____959 = nm_to_string x  in Prims.strcat "Tm_name: " uu____959
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____961 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____961
    | FStar_Syntax_Syntax.Tm_uinst uu____962 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____969 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____970 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____971,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____972;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____987,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_dynamic ;
                     FStar_Syntax_Syntax.antiquotes = uu____988;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1003 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1020 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1033 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1040 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1055 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1078 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1105 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1118 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1119,m) ->
        let uu____1161 = FStar_ST.op_Bang m  in
        (match uu____1161 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1221 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1226,m) ->
        let uu____1232 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1232
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1233 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1235 =
      let uu____1236 = FStar_Options.ugly ()  in Prims.op_Negation uu____1236
       in
    if uu____1235
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1244 = FStar_Options.print_implicits ()  in
         if uu____1244 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1248 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1273,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1293 =
             let uu____1294 =
               let uu____1303 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1303  in
             uu____1294 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1293
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1358;_})
           ->
           let uu____1373 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1373
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1375;_})
           ->
           let uu____1390 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1390
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1408 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1436 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1454  ->
                                 match uu____1454 with
                                 | (t1,uu____1460) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1436
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1408 (FStar_String.concat "\\/")  in
           let uu____1465 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1465
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1477 = tag_of_term t  in
           let uu____1478 = sli m  in
           let uu____1479 = term_to_string t'  in
           let uu____1480 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1477 uu____1478
             uu____1479 uu____1480
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1493 = tag_of_term t  in
           let uu____1494 = term_to_string t'  in
           let uu____1495 = sli m0  in
           let uu____1496 = sli m1  in
           let uu____1497 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1493
             uu____1494 uu____1495 uu____1496 uu____1497
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1506 = FStar_Range.string_of_range r  in
           let uu____1507 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1506
             uu____1507
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1514 = lid_to_string l  in
           let uu____1515 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1516 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1514 uu____1515
             uu____1516
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1518) ->
           let uu____1523 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1523
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1525 = db_to_string x3  in
           let uu____1526 =
             let uu____1527 =
               let uu____1528 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1528 ")"  in
             Prims.strcat ":(" uu____1527  in
           Prims.strcat uu____1525 uu____1526
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar u ->
           uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1534 = FStar_Options.print_universes ()  in
           if uu____1534
           then
             let uu____1535 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1535
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1555 = binders_to_string " -> " bs  in
           let uu____1556 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1555 uu____1556
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1581 = binders_to_string " " bs  in
                let uu____1582 = term_to_string t2  in
                let uu____1583 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1587 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1587)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1581 uu____1582
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1583
            | uu____1590 ->
                let uu____1593 = binders_to_string " " bs  in
                let uu____1594 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1593 uu____1594)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1601 = bv_to_string xt  in
           let uu____1602 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1603 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1601 uu____1602 uu____1603
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1628 = term_to_string t  in
           let uu____1629 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1628 uu____1629
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1648 = lbs_to_string [] lbs  in
           let uu____1649 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1648 uu____1649
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1710 =
                   let uu____1711 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1711
                     (FStar_Util.dflt "default")
                    in
                 let uu____1716 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1710 uu____1716
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1732 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1732
              in
           let uu____1733 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1733 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1772 = term_to_string head1  in
           let uu____1773 =
             let uu____1774 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1804  ->
                       match uu____1804 with
                       | (p,wopt,e) ->
                           let uu____1820 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1821 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1823 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1823
                              in
                           let uu____1824 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1820
                             uu____1821 uu____1824))
                in
             FStar_Util.concat_l "\n\t|" uu____1774  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1772 uu____1773
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1831 = FStar_Options.print_universes ()  in
           if uu____1831
           then
             let uu____1832 = term_to_string t  in
             let uu____1833 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1832 uu____1833
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1836 =
      let uu____1837 = FStar_Options.ugly ()  in Prims.op_Negation uu____1837
       in
    if uu____1836
    then
      let e =
        let uu____1839 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1839  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1862 = fv_to_string l  in
           let uu____1863 =
             let uu____1864 =
               FStar_List.map
                 (fun uu____1875  ->
                    match uu____1875 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1864 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1862 uu____1863
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1887) ->
           let uu____1892 = FStar_Options.print_bound_var_types ()  in
           if uu____1892
           then
             let uu____1893 = bv_to_string x1  in
             let uu____1894 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1893 uu____1894
           else
             (let uu____1896 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1896)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1898 = FStar_Options.print_bound_var_types ()  in
           if uu____1898
           then
             let uu____1899 = bv_to_string x1  in
             let uu____1900 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1899 uu____1900
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1904 = FStar_Options.print_real_names ()  in
           if uu____1904
           then
             let uu____1905 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1905
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1917 = quals_to_string' quals  in
      let uu____1918 =
        let uu____1919 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1935 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1936 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1937 =
                    let uu____1938 = FStar_Options.print_universes ()  in
                    if uu____1938
                    then
                      let uu____1939 =
                        let uu____1940 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1940 ">"  in
                      Prims.strcat "<" uu____1939
                    else ""  in
                  let uu____1942 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1943 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1935
                    uu____1936 uu____1937 uu____1942 uu____1943))
           in
        FStar_Util.concat_l "\n and " uu____1919  in
      FStar_Util.format3 "%slet %s %s" uu____1917
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1918

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___73_1947  ->
    match uu___73_1947 with
    | [] -> ""
    | tms ->
        let uu____1953 =
          let uu____1954 =
            FStar_List.map
              (fun t  ->
                 let uu____1960 = term_to_string t  in paren uu____1960) tms
             in
          FStar_All.pipe_right uu____1954 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1953

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1964 = FStar_Options.print_effect_args ()  in
    if uu____1964
    then
      let uu____1965 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1965
    else
      (let uu____1967 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1968 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1967 uu____1968)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___74_1969  ->
    match uu___74_1969 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1970 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1973 = aqual_to_string aq  in Prims.strcat uu____1973 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____1980 =
        let uu____1981 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1981  in
      if uu____1980
      then
        let uu____1982 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1982 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1988 = b  in
         match uu____1988 with
         | (a,imp) ->
             let uu____1995 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1995
             then
               let uu____1996 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1996
             else
               (let uu____1998 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2000 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2000)
                   in
                if uu____1998
                then
                  let uu____2001 = nm_to_string a  in
                  imp_to_string uu____2001 imp
                else
                  (let uu____2003 =
                     let uu____2004 = nm_to_string a  in
                     let uu____2005 =
                       let uu____2006 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2006  in
                     Prims.strcat uu____2004 uu____2005  in
                   imp_to_string uu____2003 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  = fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2018 = FStar_Options.print_implicits ()  in
        if uu____2018 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2022 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2022 (FStar_String.concat sep)
      else
        (let uu____2040 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2040 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___75_2049  ->
    match uu___75_2049 with
    | (a,imp) ->
        let uu____2056 = term_to_string a  in imp_to_string uu____2056 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2065 = FStar_Options.print_implicits ()  in
      if uu____2065 then args else filter_imp args  in
    let uu____2075 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2075 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2094 = FStar_Options.ugly ()  in
      if uu____2094
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2099 =
      let uu____2100 = FStar_Options.ugly ()  in Prims.op_Negation uu____2100
       in
    if uu____2099
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2114 =
             let uu____2115 = FStar_Syntax_Subst.compress t  in
             uu____2115.FStar_Syntax_Syntax.n  in
           (match uu____2114 with
            | FStar_Syntax_Syntax.Tm_type uu____2118 when
                let uu____2119 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2119 -> term_to_string t
            | uu____2120 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2122 = univ_to_string u  in
                     let uu____2123 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2122 uu____2123
                 | uu____2124 ->
                     let uu____2127 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2127))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2138 =
             let uu____2139 = FStar_Syntax_Subst.compress t  in
             uu____2139.FStar_Syntax_Syntax.n  in
           (match uu____2138 with
            | FStar_Syntax_Syntax.Tm_type uu____2142 when
                let uu____2143 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2143 -> term_to_string t
            | uu____2144 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2146 = univ_to_string u  in
                     let uu____2147 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2146 uu____2147
                 | uu____2148 ->
                     let uu____2151 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2151))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2154 = FStar_Options.print_effect_args ()  in
             if uu____2154
             then
               let uu____2155 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2156 =
                 let uu____2157 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2157 (FStar_String.concat ", ")
                  in
               let uu____2166 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2167 =
                 let uu____2168 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2168 (FStar_String.concat ", ")
                  in
               let uu____2185 =
                 let uu____2186 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2186 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2155
                 uu____2156 uu____2166 uu____2167 uu____2185
             else
               (let uu____2196 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___76_2200  ->
                           match uu___76_2200 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2201 -> false)))
                    &&
                    (let uu____2203 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2203)
                   in
                if uu____2196
                then
                  let uu____2204 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2204
                else
                  (let uu____2206 =
                     ((let uu____2209 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2209) &&
                        (let uu____2211 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2211))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2206
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2213 =
                        (let uu____2216 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2216) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___77_2220  ->
                                   match uu___77_2220 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2221 -> false)))
                         in
                      if uu____2213
                      then
                        let uu____2222 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2222
                      else
                        (let uu____2224 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2225 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2224 uu____2225))))
              in
           let dec =
             let uu____2227 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___78_2237  ->
                       match uu___78_2237 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2243 =
                             let uu____2244 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2244
                              in
                           [uu____2243]
                       | uu____2245 -> []))
                in
             FStar_All.pipe_right uu____2227 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2249 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___79_2255  ->
    match uu___79_2255 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2268 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2296 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2314  ->
                              match uu____2314 with
                              | (t,uu____2320) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2296
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2268 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2326 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2326
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2329) ->
        let uu____2330 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2330
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2338 = sli m  in
        let uu____2339 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2338 uu____2339
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2347 = sli m  in
        let uu____2348 = sli m'  in
        let uu____2349 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2347
          uu____2348 uu____2349

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2360 = FStar_Options.ugly ()  in
      if uu____2360
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
      let uu____2374 = b  in
      match uu____2374 with
      | (a,imp) ->
          let n1 =
            let uu____2378 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2378
            then FStar_Util.JsonNull
            else
              (let uu____2380 =
                 let uu____2381 = nm_to_string a  in
                 imp_to_string uu____2381 imp  in
               FStar_Util.JsonStr uu____2380)
             in
          let t =
            let uu____2383 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2383  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2406 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2406
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2418 = FStar_Options.print_universes ()  in
    if uu____2418 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2425 =
      let uu____2426 = FStar_Options.ugly ()  in Prims.op_Negation uu____2426
       in
    if uu____2425
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2430 = s  in
       match uu____2430 with
       | (us,t) ->
           let uu____2441 =
             let uu____2442 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2442  in
           let uu____2443 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2441 uu____2443)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2449 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2450 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2451 =
      let uu____2452 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2452  in
    let uu____2453 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2454 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2449 uu____2450 uu____2451
      uu____2453 uu____2454
  
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
          let uu____2479 =
            let uu____2480 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2480  in
          if uu____2479
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2494 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2494 (FStar_String.concat ",\n\t")
                in
             let uu____2503 =
               let uu____2506 =
                 let uu____2509 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2510 =
                   let uu____2513 =
                     let uu____2514 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2514  in
                   let uu____2515 =
                     let uu____2518 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2519 =
                       let uu____2522 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2523 =
                         let uu____2526 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2527 =
                           let uu____2530 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2531 =
                             let uu____2534 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2535 =
                               let uu____2538 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2539 =
                                 let uu____2542 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2543 =
                                   let uu____2546 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2547 =
                                     let uu____2550 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2551 =
                                       let uu____2554 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2555 =
                                         let uu____2558 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2559 =
                                           let uu____2562 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2563 =
                                             let uu____2566 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2567 =
                                               let uu____2570 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2571 =
                                                 let uu____2574 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2575 =
                                                   let uu____2578 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2578]  in
                                                 uu____2574 :: uu____2575  in
                                               uu____2570 :: uu____2571  in
                                             uu____2566 :: uu____2567  in
                                           uu____2562 :: uu____2563  in
                                         uu____2558 :: uu____2559  in
                                       uu____2554 :: uu____2555  in
                                     uu____2550 :: uu____2551  in
                                   uu____2546 :: uu____2547  in
                                 uu____2542 :: uu____2543  in
                               uu____2538 :: uu____2539  in
                             uu____2534 :: uu____2535  in
                           uu____2530 :: uu____2531  in
                         uu____2526 :: uu____2527  in
                       uu____2522 :: uu____2523  in
                     uu____2518 :: uu____2519  in
                   uu____2513 :: uu____2515  in
                 uu____2509 :: uu____2510  in
               (if for_free then "_for_free " else "") :: uu____2506  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2503)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2595 =
      let uu____2596 = FStar_Options.ugly ()  in Prims.op_Negation uu____2596
       in
    if uu____2595
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2602 -> ""
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
             (lid,univs1,tps,k,uu____2613,uu____2614) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2626 = FStar_Options.print_universes ()  in
             if uu____2626
             then
               let uu____2627 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2627 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2632,uu____2633,uu____2634) ->
             let uu____2639 = FStar_Options.print_universes ()  in
             if uu____2639
             then
               let uu____2640 = univ_names_to_string univs1  in
               let uu____2641 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2640
                 lid.FStar_Ident.str uu____2641
             else
               (let uu____2643 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2643)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2647 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2648 =
               let uu____2649 = FStar_Options.print_universes ()  in
               if uu____2649
               then
                 let uu____2650 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2650
               else ""  in
             let uu____2652 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2647
               lid.FStar_Ident.str uu____2648 uu____2652
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2654,f) ->
             let uu____2656 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2656
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2658) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2664 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2664
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2666) ->
             let uu____2675 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2675 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2705) -> lift_wp
               | (uu____2712,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2720 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2720 with
              | (us,t) ->
                  let uu____2727 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2728 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2729 = univ_names_to_string us  in
                  let uu____2730 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2727 uu____2728 uu____2729 uu____2730)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2740 = FStar_Options.print_universes ()  in
             if uu____2740
             then
               let uu____2741 =
                 let uu____2746 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2746  in
               (match uu____2741 with
                | (univs2,t) ->
                    let uu____2757 =
                      let uu____2770 =
                        let uu____2771 = FStar_Syntax_Subst.compress t  in
                        uu____2771.FStar_Syntax_Syntax.n  in
                      match uu____2770 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2812 -> failwith "impossible"  in
                    (match uu____2757 with
                     | (tps1,c1) ->
                         let uu____2843 = sli l  in
                         let uu____2844 = univ_names_to_string univs2  in
                         let uu____2845 = binders_to_string " " tps1  in
                         let uu____2846 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2843 uu____2844 uu____2845 uu____2846))
             else
               (let uu____2848 = sli l  in
                let uu____2849 = binders_to_string " " tps  in
                let uu____2850 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2848 uu____2849
                  uu____2850)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2857 =
               let uu____2858 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2858  in
             let uu____2863 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2857 uu____2863
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2864 ->
           let uu____2867 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2867 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2878 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2878 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2884,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2886;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2888;
                       FStar_Syntax_Syntax.lbdef = uu____2889;
                       FStar_Syntax_Syntax.lbattrs = uu____2890;
                       FStar_Syntax_Syntax.lbpos = uu____2891;_}::[]),uu____2892)
        ->
        let uu____2913 = lbname_to_string lb  in
        let uu____2914 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2913 uu____2914
    | uu____2915 ->
        let uu____2916 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2916 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2932 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2933 =
      let uu____2934 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2934 (FStar_String.concat "\n")  in
    let uu____2939 =
      let uu____2940 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2940 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2932 uu____2933 uu____2939
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___80_2949  ->
    match uu___80_2949 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2952 = FStar_Util.string_of_int i  in
        let uu____2953 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2952 uu____2953
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2956 = bv_to_string x  in
        let uu____2957 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2956 uu____2957
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2964 = bv_to_string x  in
        let uu____2965 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2964 uu____2965
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2968 = FStar_Util.string_of_int i  in
        let uu____2969 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2968 uu____2969
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2972 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2972
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2978 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2978 (FStar_String.concat "; ")
  
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
          (let uu____3016 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3016))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3023 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3023)));
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
           (let uu____3057 = f x  in
            FStar_Util.string_builder_append strb uu____3057);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3064 = f x1  in
                 FStar_Util.string_builder_append strb uu____3064)) xs;
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
           (let uu____3102 = f x  in
            FStar_Util.string_builder_append strb uu____3102);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3109 = f x1  in
                 FStar_Util.string_builder_append strb uu____3109)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3125 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3125
  
let (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____3135 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____3136 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____3137 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format3 "(%s |- %s : %s)" uu____3135 uu____3136 uu____3137
  