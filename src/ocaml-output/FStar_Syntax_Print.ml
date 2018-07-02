open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___199_5  ->
    match uu___199_5 with
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
  fun uu___200_281  ->
    match uu___200_281 with
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
         (fun uu___201_347  ->
            match uu___201_347 with
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
        let uu____432 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____432
        then
          let uu____437 =
            let uu____442 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____442  in
          (match uu____437 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____452 =
                 let uu____455 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____455 :: xs  in
               FStar_Pervasives_Native.Some uu____452
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____465 ->
        let uu____466 = is_lex_top e  in
        if uu____466
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____507 = f hd1  in if uu____507 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____531 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____531
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____555 = get_lid e  in find_lid uu____555 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____565 = get_lid e  in find_lid uu____565 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____575 = get_lid t  in find_lid uu____575 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___202_585  ->
    match uu___202_585 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____593 = FStar_Options.hide_uvar_nums ()  in
    if uu____593
    then "?"
    else
      (let uu____595 =
         let uu____596 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____596 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____595)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____602 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____603 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____602 uu____603
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
     FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun u  ->
    let uu____625 = FStar_Options.hide_uvar_nums ()  in
    if uu____625
    then "?"
    else
      (let uu____627 =
         let uu____628 =
           let uu____629 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____629 FStar_Util.string_of_int  in
         let uu____630 =
           let uu____631 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____631  in
         Prims.strcat uu____628 uu____630  in
       Prims.strcat "?" uu____627)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____652 = FStar_Syntax_Subst.compress_univ u  in
      match uu____652 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____662 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____670 =
      let uu____671 = FStar_Options.ugly ()  in Prims.op_Negation uu____671
       in
    if uu____670
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____675 = FStar_Syntax_Subst.compress_univ u  in
       match uu____675 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____687 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____687
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____689 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____689 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____703 = univ_to_string u2  in
                let uu____704 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____703 uu____704)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____708 =
             let uu____709 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____709 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____708
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____723 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____723 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____733 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____733 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___203_744  ->
    match uu___203_744 with
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
        let uu____746 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____746
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____749 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____749 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____760 =
          let uu____761 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____761  in
        let uu____762 =
          let uu____763 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____763 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____760 uu____762
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____782 =
          let uu____783 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____783  in
        let uu____784 =
          let uu____785 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____785 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____782 uu____784
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____795 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____795
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
    | uu____806 ->
        let uu____809 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____809 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____827 ->
        let uu____830 = quals_to_string quals  in Prims.strcat uu____830 " "
  
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
    | FStar_Syntax_Syntax.Tm_arrow uu____1033 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1046 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1053 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1068 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1091 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1118 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1131 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1144,m) ->
        let uu____1182 = FStar_ST.op_Bang m  in
        (match uu____1182 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1238 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1243,m) ->
        let uu____1249 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1249
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1250 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1252 =
      let uu____1253 = FStar_Options.ugly ()  in Prims.op_Negation uu____1253
       in
    if uu____1252
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1261 = FStar_Options.print_implicits ()  in
         if uu____1261 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1265 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1288,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1308 =
             let uu____1309 =
               let uu____1318 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1318  in
             uu____1309 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1308
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1369;_})
           ->
           let uu____1384 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1384
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1386;_})
           ->
           let uu____1401 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1401
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1419 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1447 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1465  ->
                                 match uu____1465 with
                                 | (t1,uu____1471) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1447
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1419 (FStar_String.concat "\\/")  in
           let uu____1476 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1476
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1488 = tag_of_term t  in
           let uu____1489 = sli m  in
           let uu____1490 = term_to_string t'  in
           let uu____1491 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1488 uu____1489
             uu____1490 uu____1491
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1504 = tag_of_term t  in
           let uu____1505 = term_to_string t'  in
           let uu____1506 = sli m0  in
           let uu____1507 = sli m1  in
           let uu____1508 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1504
             uu____1505 uu____1506 uu____1507 uu____1508
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1517 = FStar_Range.string_of_range r  in
           let uu____1518 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1517
             uu____1518
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1525 = lid_to_string l  in
           let uu____1526 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1527 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1525 uu____1526
             uu____1527
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1529) ->
           let uu____1534 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1534
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1536 = db_to_string x3  in
           let uu____1537 =
             let uu____1538 =
               let uu____1539 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1539 ")"  in
             Prims.strcat ":(" uu____1538  in
           Prims.strcat uu____1536 uu____1537
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1543)) ->
           let uu____1558 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1558
           then ctx_uvar_to_string u
           else
             (let uu____1560 =
                let uu____1561 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1561  in
              Prims.strcat "?" uu____1560)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1580 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1580
           then
             let uu____1581 = ctx_uvar_to_string u  in
             let uu____1582 =
               let uu____1583 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1583 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1581 uu____1582
           else
             (let uu____1595 =
                let uu____1596 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1596  in
              Prims.strcat "?" uu____1595)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1599 = FStar_Options.print_universes ()  in
           if uu____1599
           then
             let uu____1600 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1600
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1620 = binders_to_string " -> " bs  in
           let uu____1621 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1620 uu____1621
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1646 = binders_to_string " " bs  in
                let uu____1647 = term_to_string t2  in
                let uu____1648 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1652 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1652)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1646 uu____1647
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1648
            | uu____1655 ->
                let uu____1658 = binders_to_string " " bs  in
                let uu____1659 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1658 uu____1659)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1666 = bv_to_string xt  in
           let uu____1667 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1668 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1666 uu____1667 uu____1668
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1693 = term_to_string t  in
           let uu____1694 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1693 uu____1694
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1713 = lbs_to_string [] lbs  in
           let uu____1714 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1713 uu____1714
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1775 =
                   let uu____1776 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1776
                     (FStar_Util.dflt "default")
                    in
                 let uu____1781 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1775 uu____1781
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1797 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1797
              in
           let uu____1798 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1798 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1837 = term_to_string head1  in
           let uu____1838 =
             let uu____1839 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1869  ->
                       match uu____1869 with
                       | (p,wopt,e) ->
                           let uu____1885 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1886 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1888 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1888
                              in
                           let uu____1889 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1885
                             uu____1886 uu____1889))
                in
             FStar_Util.concat_l "\n\t|" uu____1839  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1837 uu____1838
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1896 = FStar_Options.print_universes ()  in
           if uu____1896
           then
             let uu____1897 = term_to_string t  in
             let uu____1898 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1897 uu____1898
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1901 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1902 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1903 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1901 uu____1902
      uu____1903

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___204_1904  ->
    match uu___204_1904 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1907 = FStar_Util.string_of_int i  in
        let uu____1908 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1907 uu____1908
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1911 = bv_to_string x  in
        let uu____1912 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1911 uu____1912
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1919 = bv_to_string x  in
        let uu____1920 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____1919 uu____1920
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1923 = FStar_Util.string_of_int i  in
        let uu____1924 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1923 uu____1924
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1927 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1927

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1929 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1929 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1939 =
      let uu____1940 = FStar_Options.ugly ()  in Prims.op_Negation uu____1940
       in
    if uu____1939
    then
      let e =
        let uu____1942 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1942  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1965 = fv_to_string l  in
           let uu____1966 =
             let uu____1967 =
               FStar_List.map
                 (fun uu____1978  ->
                    match uu____1978 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1967 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1965 uu____1966
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1990) ->
           let uu____1995 = FStar_Options.print_bound_var_types ()  in
           if uu____1995
           then
             let uu____1996 = bv_to_string x1  in
             let uu____1997 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1996 uu____1997
           else
             (let uu____1999 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1999)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2001 = FStar_Options.print_bound_var_types ()  in
           if uu____2001
           then
             let uu____2002 = bv_to_string x1  in
             let uu____2003 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2002 uu____2003
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2007 = FStar_Options.print_real_names ()  in
           if uu____2007
           then
             let uu____2008 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2008
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2020 = quals_to_string' quals  in
      let uu____2021 =
        let uu____2022 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2038 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2039 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2040 =
                    let uu____2041 = FStar_Options.print_universes ()  in
                    if uu____2041
                    then
                      let uu____2042 =
                        let uu____2043 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2043 ">"  in
                      Prims.strcat "<" uu____2042
                    else ""  in
                  let uu____2045 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2046 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2038
                    uu____2039 uu____2040 uu____2045 uu____2046))
           in
        FStar_Util.concat_l "\n and " uu____2022  in
      FStar_Util.format3 "%slet %s %s" uu____2020
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2021

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___205_2050  ->
    match uu___205_2050 with
    | [] -> ""
    | tms ->
        let uu____2056 =
          let uu____2057 =
            FStar_List.map
              (fun t  ->
                 let uu____2063 = term_to_string t  in paren uu____2063) tms
             in
          FStar_All.pipe_right uu____2057 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2056

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2067 = FStar_Options.print_effect_args ()  in
    if uu____2067
    then
      let uu____2068 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2068
    else
      (let uu____2070 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2071 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2070 uu____2071)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___206_2072  ->
    match uu___206_2072 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2073 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2076 = aqual_to_string aq  in Prims.strcat uu____2076 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2083 =
        let uu____2084 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2084  in
      if uu____2083
      then
        let uu____2085 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2085 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2091 = b  in
         match uu____2091 with
         | (a,imp) ->
             let uu____2098 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2098
             then
               let uu____2099 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2099
             else
               (let uu____2101 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2103 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2103)
                   in
                if uu____2101
                then
                  let uu____2104 = nm_to_string a  in
                  imp_to_string uu____2104 imp
                else
                  (let uu____2106 =
                     let uu____2107 = nm_to_string a  in
                     let uu____2108 =
                       let uu____2109 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2109  in
                     Prims.strcat uu____2107 uu____2108  in
                   imp_to_string uu____2106 imp)))

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
        let uu____2121 = FStar_Options.print_implicits ()  in
        if uu____2121 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2125 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2125 (FStar_String.concat sep)
      else
        (let uu____2143 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2143 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___207_2152  ->
    match uu___207_2152 with
    | (a,imp) ->
        let uu____2159 = term_to_string a  in imp_to_string uu____2159 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2168 = FStar_Options.print_implicits ()  in
      if uu____2168 then args else filter_imp args  in
    let uu____2178 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2178 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2197 = FStar_Options.ugly ()  in
      if uu____2197
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2202 =
      let uu____2203 = FStar_Options.ugly ()  in Prims.op_Negation uu____2203
       in
    if uu____2202
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2217 =
             let uu____2218 = FStar_Syntax_Subst.compress t  in
             uu____2218.FStar_Syntax_Syntax.n  in
           (match uu____2217 with
            | FStar_Syntax_Syntax.Tm_type uu____2221 when
                let uu____2222 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2222 -> term_to_string t
            | uu____2223 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2225 = univ_to_string u  in
                     let uu____2226 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2225 uu____2226
                 | uu____2227 ->
                     let uu____2230 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2230))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2241 =
             let uu____2242 = FStar_Syntax_Subst.compress t  in
             uu____2242.FStar_Syntax_Syntax.n  in
           (match uu____2241 with
            | FStar_Syntax_Syntax.Tm_type uu____2245 when
                let uu____2246 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2246 -> term_to_string t
            | uu____2247 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2249 = univ_to_string u  in
                     let uu____2250 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2249 uu____2250
                 | uu____2251 ->
                     let uu____2254 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2254))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2257 = FStar_Options.print_effect_args ()  in
             if uu____2257
             then
               let uu____2258 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2259 =
                 let uu____2260 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2260 (FStar_String.concat ", ")
                  in
               let uu____2269 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2270 =
                 let uu____2271 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2271 (FStar_String.concat ", ")
                  in
               let uu____2288 =
                 let uu____2289 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2289 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2258
                 uu____2259 uu____2269 uu____2270 uu____2288
             else
               (let uu____2299 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___208_2303  ->
                           match uu___208_2303 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2304 -> false)))
                    &&
                    (let uu____2306 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2306)
                   in
                if uu____2299
                then
                  let uu____2307 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2307
                else
                  (let uu____2309 =
                     ((let uu____2312 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2312) &&
                        (let uu____2314 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2314))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2309
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2316 =
                        (let uu____2319 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2319) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___209_2323  ->
                                   match uu___209_2323 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2324 -> false)))
                         in
                      if uu____2316
                      then
                        let uu____2325 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2325
                      else
                        (let uu____2327 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2328 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2327 uu____2328))))
              in
           let dec =
             let uu____2330 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___210_2340  ->
                       match uu___210_2340 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2346 =
                             let uu____2347 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2347
                              in
                           [uu____2346]
                       | uu____2348 -> []))
                in
             FStar_All.pipe_right uu____2330 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2352 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___211_2358  ->
    match uu___211_2358 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2371 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2399 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2417  ->
                              match uu____2417 with
                              | (t,uu____2423) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2399
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2371 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2429 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2429
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2432) ->
        let uu____2433 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2433
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2441 = sli m  in
        let uu____2442 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2441 uu____2442
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2450 = sli m  in
        let uu____2451 = sli m'  in
        let uu____2452 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2450
          uu____2451 uu____2452

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2463 = FStar_Options.ugly ()  in
      if uu____2463
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
      let uu____2477 = b  in
      match uu____2477 with
      | (a,imp) ->
          let n1 =
            let uu____2481 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2481
            then FStar_Util.JsonNull
            else
              (let uu____2483 =
                 let uu____2484 = nm_to_string a  in
                 imp_to_string uu____2484 imp  in
               FStar_Util.JsonStr uu____2483)
             in
          let t =
            let uu____2486 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2486  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2509 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2509
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2521 = FStar_Options.print_universes ()  in
    if uu____2521 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2528 =
      let uu____2529 = FStar_Options.ugly ()  in Prims.op_Negation uu____2529
       in
    if uu____2528
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2533 = s  in
       match uu____2533 with
       | (us,t) ->
           let uu____2544 =
             let uu____2545 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2545  in
           let uu____2546 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2544 uu____2546)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2552 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2553 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2554 =
      let uu____2555 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2555  in
    let uu____2556 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2557 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2552 uu____2553 uu____2554
      uu____2556 uu____2557
  
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
          let uu____2582 =
            let uu____2583 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2583  in
          if uu____2582
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2597 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2597 (FStar_String.concat ",\n\t")
                in
             let uu____2606 =
               let uu____2609 =
                 let uu____2612 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2613 =
                   let uu____2616 =
                     let uu____2617 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2617  in
                   let uu____2618 =
                     let uu____2621 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2622 =
                       let uu____2625 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2626 =
                         let uu____2629 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2630 =
                           let uu____2633 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2634 =
                             let uu____2637 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2638 =
                               let uu____2641 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2642 =
                                 let uu____2645 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2646 =
                                   let uu____2649 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2650 =
                                     let uu____2653 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2654 =
                                       let uu____2657 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2658 =
                                         let uu____2661 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2662 =
                                           let uu____2665 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2666 =
                                             let uu____2669 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2670 =
                                               let uu____2673 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2674 =
                                                 let uu____2677 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2678 =
                                                   let uu____2681 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2681]  in
                                                 uu____2677 :: uu____2678  in
                                               uu____2673 :: uu____2674  in
                                             uu____2669 :: uu____2670  in
                                           uu____2665 :: uu____2666  in
                                         uu____2661 :: uu____2662  in
                                       uu____2657 :: uu____2658  in
                                     uu____2653 :: uu____2654  in
                                   uu____2649 :: uu____2650  in
                                 uu____2645 :: uu____2646  in
                               uu____2641 :: uu____2642  in
                             uu____2637 :: uu____2638  in
                           uu____2633 :: uu____2634  in
                         uu____2629 :: uu____2630  in
                       uu____2625 :: uu____2626  in
                     uu____2621 :: uu____2622  in
                   uu____2616 :: uu____2618  in
                 uu____2612 :: uu____2613  in
               (if for_free then "_for_free " else "") :: uu____2609  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2606)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2698 =
      let uu____2699 = FStar_Options.ugly ()  in Prims.op_Negation uu____2699
       in
    if uu____2698
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2705 -> ""
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
             (lid,univs1,tps,k,uu____2716,uu____2717) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2729 = FStar_Options.print_universes ()  in
             if uu____2729
             then
               let uu____2730 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2730 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2735,uu____2736,uu____2737) ->
             let uu____2742 = FStar_Options.print_universes ()  in
             if uu____2742
             then
               let uu____2743 = univ_names_to_string univs1  in
               let uu____2744 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2743
                 lid.FStar_Ident.str uu____2744
             else
               (let uu____2746 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2746)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2750 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2751 =
               let uu____2752 = FStar_Options.print_universes ()  in
               if uu____2752
               then
                 let uu____2753 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2753
               else ""  in
             let uu____2755 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2750
               lid.FStar_Ident.str uu____2751 uu____2755
         | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
             let uu____2759 = FStar_Options.print_universes ()  in
             if uu____2759
             then
               let uu____2760 = univ_names_to_string us  in
               let uu____2761 = term_to_string f  in
               FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
                 uu____2760 uu____2761
             else
               (let uu____2763 = term_to_string f  in
                FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str
                  uu____2763)
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2765) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2771 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2771
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2773) ->
             let uu____2782 =
               let uu____2783 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2783 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2782
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2819) -> lift_wp
               | (uu____2826,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2834 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2834 with
              | (us,t) ->
                  let uu____2845 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2846 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2847 = univ_names_to_string us  in
                  let uu____2848 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2845 uu____2846 uu____2847 uu____2848)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2858 = FStar_Options.print_universes ()  in
             if uu____2858
             then
               let uu____2859 =
                 let uu____2864 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2864  in
               (match uu____2859 with
                | (univs2,t) ->
                    let uu____2875 =
                      let uu____2880 =
                        let uu____2881 = FStar_Syntax_Subst.compress t  in
                        uu____2881.FStar_Syntax_Syntax.n  in
                      match uu____2880 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2906 -> failwith "impossible"  in
                    (match uu____2875 with
                     | (tps1,c1) ->
                         let uu____2913 = sli l  in
                         let uu____2914 = univ_names_to_string univs2  in
                         let uu____2915 = binders_to_string " " tps1  in
                         let uu____2916 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2913 uu____2914 uu____2915 uu____2916))
             else
               (let uu____2918 = sli l  in
                let uu____2919 = binders_to_string " " tps  in
                let uu____2920 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2918 uu____2919
                  uu____2920)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2927 =
               let uu____2928 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2928  in
             let uu____2933 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2927 uu____2933
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2934 ->
           let uu____2937 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2937 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2948 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2948 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2954,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2956;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2958;
                       FStar_Syntax_Syntax.lbdef = uu____2959;
                       FStar_Syntax_Syntax.lbattrs = uu____2960;
                       FStar_Syntax_Syntax.lbpos = uu____2961;_}::[]),uu____2962)
        ->
        let uu____2983 = lbname_to_string lb  in
        let uu____2984 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2983 uu____2984
    | uu____2985 ->
        let uu____2986 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2986 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3002 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3003 =
      let uu____3004 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3004 (FStar_String.concat "\n")  in
    let uu____3009 =
      let uu____3010 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3010 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3002 uu____3003 uu____3009
  
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
          (let uu____3044 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3044))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3051 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3051)));
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
           (let uu____3085 = f x  in
            FStar_Util.string_builder_append strb uu____3085);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3092 = f x1  in
                 FStar_Util.string_builder_append strb uu____3092)) xs;
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
           (let uu____3130 = f x  in
            FStar_Util.string_builder_append strb uu____3130);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3137 = f x1  in
                 FStar_Util.string_builder_append strb uu____3137)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3153 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3153
  