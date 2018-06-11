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
  fun uu___203_585  ->
    match uu___203_585 with
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
  fun uu___204_744  ->
    match uu___204_744 with
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
         | FStar_Pervasives_Native.Some uu____1242 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1247,m) ->
        let uu____1253 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1253
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1254 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1256 =
      let uu____1257 = FStar_Options.ugly ()  in Prims.op_Negation uu____1257
       in
    if uu____1256
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1265 = FStar_Options.print_implicits ()  in
         if uu____1265 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1269 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1292,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1312 =
             let uu____1313 =
               let uu____1322 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1322  in
             uu____1313 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1312
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1377;_})
           ->
           let uu____1392 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1392
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1394;_})
           ->
           let uu____1409 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1409
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1427 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1455 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1473  ->
                                 match uu____1473 with
                                 | (t1,uu____1479) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1455
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1427 (FStar_String.concat "\\/")  in
           let uu____1484 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1484
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1496 = tag_of_term t  in
           let uu____1497 = sli m  in
           let uu____1498 = term_to_string t'  in
           let uu____1499 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1496 uu____1497
             uu____1498 uu____1499
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1512 = tag_of_term t  in
           let uu____1513 = term_to_string t'  in
           let uu____1514 = sli m0  in
           let uu____1515 = sli m1  in
           let uu____1516 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1512
             uu____1513 uu____1514 uu____1515 uu____1516
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1525 = FStar_Range.string_of_range r  in
           let uu____1526 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1525
             uu____1526
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1533 = lid_to_string l  in
           let uu____1534 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1535 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1533 uu____1534
             uu____1535
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1537) ->
           let uu____1542 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1542
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1544 = db_to_string x3  in
           let uu____1545 =
             let uu____1546 =
               let uu____1547 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1547 ")"  in
             Prims.strcat ":(" uu____1546  in
           Prims.strcat uu____1544 uu____1545
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1551)) ->
           let uu____1566 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1566
           then ctx_uvar_to_string u
           else
             (let uu____1568 =
                let uu____1569 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1569  in
              Prims.strcat "?" uu____1568)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1588 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1588
           then
             let uu____1589 = ctx_uvar_to_string u  in
             let uu____1590 =
               let uu____1591 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1591 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1589 uu____1590
           else
             (let uu____1603 =
                let uu____1604 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1604  in
              Prims.strcat "?" uu____1603)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1607 = FStar_Options.print_universes ()  in
           if uu____1607
           then
             let uu____1608 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1608
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1628 = binders_to_string " -> " bs  in
           let uu____1629 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1628 uu____1629
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1654 = binders_to_string " " bs  in
                let uu____1655 = term_to_string t2  in
                let uu____1656 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1660 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1660)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1654 uu____1655
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1656
            | uu____1663 ->
                let uu____1666 = binders_to_string " " bs  in
                let uu____1667 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1666 uu____1667)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1674 = bv_to_string xt  in
           let uu____1675 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1676 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1674 uu____1675 uu____1676
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1701 = term_to_string t  in
           let uu____1702 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1701 uu____1702
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1721 = lbs_to_string [] lbs  in
           let uu____1722 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1721 uu____1722
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1783 =
                   let uu____1784 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1784
                     (FStar_Util.dflt "default")
                    in
                 let uu____1789 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1783 uu____1789
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1805 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1805
              in
           let uu____1806 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1806 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1845 = term_to_string head1  in
           let uu____1846 =
             let uu____1847 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1877  ->
                       match uu____1877 with
                       | (p,wopt,e) ->
                           let uu____1893 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1894 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1896 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1896
                              in
                           let uu____1897 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1893
                             uu____1894 uu____1897))
                in
             FStar_Util.concat_l "\n\t|" uu____1847  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1845 uu____1846
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1904 = FStar_Options.print_universes ()  in
           if uu____1904
           then
             let uu____1905 = term_to_string t  in
             let uu____1906 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1905 uu____1906
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1909 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1910 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1911 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1909 uu____1910
      uu____1911

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___205_1912  ->
    match uu___205_1912 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1915 = FStar_Util.string_of_int i  in
        let uu____1916 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1915 uu____1916
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1919 = bv_to_string x  in
        let uu____1920 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1919 uu____1920
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1927 = bv_to_string x  in
        let uu____1928 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____1927 uu____1928
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1931 = FStar_Util.string_of_int i  in
        let uu____1932 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1931 uu____1932
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1935 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1935

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1937 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1937 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1947 =
      let uu____1948 = FStar_Options.ugly ()  in Prims.op_Negation uu____1948
       in
    if uu____1947
    then
      let e =
        let uu____1950 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1950  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1973 = fv_to_string l  in
           let uu____1974 =
             let uu____1975 =
               FStar_List.map
                 (fun uu____1986  ->
                    match uu____1986 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1975 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1973 uu____1974
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1998) ->
           let uu____2003 = FStar_Options.print_bound_var_types ()  in
           if uu____2003
           then
             let uu____2004 = bv_to_string x1  in
             let uu____2005 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2004 uu____2005
           else
             (let uu____2007 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2007)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2009 = FStar_Options.print_bound_var_types ()  in
           if uu____2009
           then
             let uu____2010 = bv_to_string x1  in
             let uu____2011 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2010 uu____2011
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2015 = FStar_Options.print_real_names ()  in
           if uu____2015
           then
             let uu____2016 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2016
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2028 = quals_to_string' quals  in
      let uu____2029 =
        let uu____2030 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2046 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2047 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2048 =
                    let uu____2049 = FStar_Options.print_universes ()  in
                    if uu____2049
                    then
                      let uu____2050 =
                        let uu____2051 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2051 ">"  in
                      Prims.strcat "<" uu____2050
                    else ""  in
                  let uu____2053 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2054 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2046
                    uu____2047 uu____2048 uu____2053 uu____2054))
           in
        FStar_Util.concat_l "\n and " uu____2030  in
      FStar_Util.format3 "%slet %s %s" uu____2028
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2029

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___206_2058  ->
    match uu___206_2058 with
    | [] -> ""
    | tms ->
        let uu____2064 =
          let uu____2065 =
            FStar_List.map
              (fun t  ->
                 let uu____2071 = term_to_string t  in paren uu____2071) tms
             in
          FStar_All.pipe_right uu____2065 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2064

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2075 = FStar_Options.print_effect_args ()  in
    if uu____2075
    then
      let uu____2076 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2076
    else
      (let uu____2078 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2079 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2078 uu____2079)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___207_2080  ->
    match uu___207_2080 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2081 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2084 = aqual_to_string aq  in Prims.strcat uu____2084 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2091 =
        let uu____2092 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2092  in
      if uu____2091
      then
        let uu____2093 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2093 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2099 = b  in
         match uu____2099 with
         | (a,imp) ->
             let uu____2106 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2106
             then
               let uu____2107 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2107
             else
               (let uu____2109 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2111 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2111)
                   in
                if uu____2109
                then
                  let uu____2112 = nm_to_string a  in
                  imp_to_string uu____2112 imp
                else
                  (let uu____2114 =
                     let uu____2115 = nm_to_string a  in
                     let uu____2116 =
                       let uu____2117 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2117  in
                     Prims.strcat uu____2115 uu____2116  in
                   imp_to_string uu____2114 imp)))

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
        let uu____2129 = FStar_Options.print_implicits ()  in
        if uu____2129 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2133 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2133 (FStar_String.concat sep)
      else
        (let uu____2151 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2151 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___208_2160  ->
    match uu___208_2160 with
    | (a,imp) ->
        let uu____2167 = term_to_string a  in imp_to_string uu____2167 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2176 = FStar_Options.print_implicits ()  in
      if uu____2176 then args else filter_imp args  in
    let uu____2186 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2186 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2205 = FStar_Options.ugly ()  in
      if uu____2205
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2210 =
      let uu____2211 = FStar_Options.ugly ()  in Prims.op_Negation uu____2211
       in
    if uu____2210
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2225 =
             let uu____2226 = FStar_Syntax_Subst.compress t  in
             uu____2226.FStar_Syntax_Syntax.n  in
           (match uu____2225 with
            | FStar_Syntax_Syntax.Tm_type uu____2229 when
                let uu____2230 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2230 -> term_to_string t
            | uu____2231 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2233 = univ_to_string u  in
                     let uu____2234 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2233 uu____2234
                 | uu____2235 ->
                     let uu____2238 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2238))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2249 =
             let uu____2250 = FStar_Syntax_Subst.compress t  in
             uu____2250.FStar_Syntax_Syntax.n  in
           (match uu____2249 with
            | FStar_Syntax_Syntax.Tm_type uu____2253 when
                let uu____2254 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2254 -> term_to_string t
            | uu____2255 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2257 = univ_to_string u  in
                     let uu____2258 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2257 uu____2258
                 | uu____2259 ->
                     let uu____2262 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2262))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2265 = FStar_Options.print_effect_args ()  in
             if uu____2265
             then
               let uu____2266 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2267 =
                 let uu____2268 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2268 (FStar_String.concat ", ")
                  in
               let uu____2277 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2278 =
                 let uu____2279 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2279 (FStar_String.concat ", ")
                  in
               let uu____2296 =
                 let uu____2297 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2297 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2266
                 uu____2267 uu____2277 uu____2278 uu____2296
             else
               (let uu____2307 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___209_2311  ->
                           match uu___209_2311 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2312 -> false)))
                    &&
                    (let uu____2314 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2314)
                   in
                if uu____2307
                then
                  let uu____2315 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2315
                else
                  (let uu____2317 =
                     ((let uu____2320 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2320) &&
                        (let uu____2322 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2322))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2317
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2324 =
                        (let uu____2327 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2327) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___210_2331  ->
                                   match uu___210_2331 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2332 -> false)))
                         in
                      if uu____2324
                      then
                        let uu____2333 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2333
                      else
                        (let uu____2335 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2336 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2335 uu____2336))))
              in
           let dec =
             let uu____2338 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___211_2348  ->
                       match uu___211_2348 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2354 =
                             let uu____2355 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2355
                              in
                           [uu____2354]
                       | uu____2356 -> []))
                in
             FStar_All.pipe_right uu____2338 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2360 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___212_2366  ->
    match uu___212_2366 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2379 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2407 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2425  ->
                              match uu____2425 with
                              | (t,uu____2431) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2407
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2379 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2437 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2437
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2440) ->
        let uu____2441 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2441
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2449 = sli m  in
        let uu____2450 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2449 uu____2450
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2458 = sli m  in
        let uu____2459 = sli m'  in
        let uu____2460 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2458
          uu____2459 uu____2460

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2471 = FStar_Options.ugly ()  in
      if uu____2471
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
      let uu____2485 = b  in
      match uu____2485 with
      | (a,imp) ->
          let n1 =
            let uu____2489 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2489
            then FStar_Util.JsonNull
            else
              (let uu____2491 =
                 let uu____2492 = nm_to_string a  in
                 imp_to_string uu____2492 imp  in
               FStar_Util.JsonStr uu____2491)
             in
          let t =
            let uu____2494 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2494  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2517 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2517
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2529 = FStar_Options.print_universes ()  in
    if uu____2529 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2536 =
      let uu____2537 = FStar_Options.ugly ()  in Prims.op_Negation uu____2537
       in
    if uu____2536
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2541 = s  in
       match uu____2541 with
       | (us,t) ->
           let uu____2552 =
             let uu____2553 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2553  in
           let uu____2554 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2552 uu____2554)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2560 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2561 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2562 =
      let uu____2563 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2563  in
    let uu____2564 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2565 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2560 uu____2561 uu____2562
      uu____2564 uu____2565
  
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
          let uu____2590 =
            let uu____2591 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2591  in
          if uu____2590
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2605 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2605 (FStar_String.concat ",\n\t")
                in
             let uu____2614 =
               let uu____2617 =
                 let uu____2620 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2621 =
                   let uu____2624 =
                     let uu____2625 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2625  in
                   let uu____2626 =
                     let uu____2629 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2630 =
                       let uu____2633 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2634 =
                         let uu____2637 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2638 =
                           let uu____2641 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2642 =
                             let uu____2645 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2646 =
                               let uu____2649 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2650 =
                                 let uu____2653 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2654 =
                                   let uu____2657 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2658 =
                                     let uu____2661 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2662 =
                                       let uu____2665 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2666 =
                                         let uu____2669 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2670 =
                                           let uu____2673 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2674 =
                                             let uu____2677 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2678 =
                                               let uu____2681 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2682 =
                                                 let uu____2685 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2686 =
                                                   let uu____2689 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2689]  in
                                                 uu____2685 :: uu____2686  in
                                               uu____2681 :: uu____2682  in
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
                   uu____2624 :: uu____2626  in
                 uu____2620 :: uu____2621  in
               (if for_free then "_for_free " else "") :: uu____2617  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2614)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2706 =
      let uu____2707 = FStar_Options.ugly ()  in Prims.op_Negation uu____2707
       in
    if uu____2706
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2713 -> ""
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
             (lid,univs1,tps,k,uu____2724,uu____2725) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2737 = FStar_Options.print_universes ()  in
             if uu____2737
             then
               let uu____2738 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2738 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2743,uu____2744,uu____2745) ->
             let uu____2750 = FStar_Options.print_universes ()  in
             if uu____2750
             then
               let uu____2751 = univ_names_to_string univs1  in
               let uu____2752 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2751
                 lid.FStar_Ident.str uu____2752
             else
               (let uu____2754 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2754)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2758 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2759 =
               let uu____2760 = FStar_Options.print_universes ()  in
               if uu____2760
               then
                 let uu____2761 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2761
               else ""  in
             let uu____2763 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2758
               lid.FStar_Ident.str uu____2759 uu____2763
         | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
             let uu____2767 = FStar_Options.print_universes ()  in
             if uu____2767
             then
               let uu____2768 = univ_names_to_string us  in
               let uu____2769 = term_to_string f  in
               FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
                 uu____2768 uu____2769
             else
               (let uu____2771 = term_to_string f  in
                FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str
                  uu____2771)
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2773) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2779 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2779
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2781) ->
             let uu____2790 =
               let uu____2791 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2791 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2790
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2827) -> lift_wp
               | (uu____2834,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2842 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2842 with
              | (us,t) ->
                  let uu____2853 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2854 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2855 = univ_names_to_string us  in
                  let uu____2856 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2853 uu____2854 uu____2855 uu____2856)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2866 = FStar_Options.print_universes ()  in
             if uu____2866
             then
               let uu____2867 =
                 let uu____2872 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2872  in
               (match uu____2867 with
                | (univs2,t) ->
                    let uu____2883 =
                      let uu____2888 =
                        let uu____2889 = FStar_Syntax_Subst.compress t  in
                        uu____2889.FStar_Syntax_Syntax.n  in
                      match uu____2888 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2914 -> failwith "impossible"  in
                    (match uu____2883 with
                     | (tps1,c1) ->
                         let uu____2921 = sli l  in
                         let uu____2922 = univ_names_to_string univs2  in
                         let uu____2923 = binders_to_string " " tps1  in
                         let uu____2924 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2921 uu____2922 uu____2923 uu____2924))
             else
               (let uu____2926 = sli l  in
                let uu____2927 = binders_to_string " " tps  in
                let uu____2928 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2926 uu____2927
                  uu____2928)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2935 =
               let uu____2936 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2936  in
             let uu____2941 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2935 uu____2941
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2942 ->
           let uu____2945 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2945 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2956 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2956 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2962,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2964;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2966;
                       FStar_Syntax_Syntax.lbdef = uu____2967;
                       FStar_Syntax_Syntax.lbattrs = uu____2968;
                       FStar_Syntax_Syntax.lbpos = uu____2969;_}::[]),uu____2970)
        ->
        let uu____2991 = lbname_to_string lb  in
        let uu____2992 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2991 uu____2992
    | uu____2993 ->
        let uu____2994 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2994 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3010 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3011 =
      let uu____3012 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3012 (FStar_String.concat "\n")  in
    let uu____3017 =
      let uu____3018 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3018 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3010 uu____3011 uu____3017
  
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
          (let uu____3052 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3052))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3059 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3059)));
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
           (let uu____3093 = f x  in
            FStar_Util.string_builder_append strb uu____3093);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3100 = f x1  in
                 FStar_Util.string_builder_append strb uu____3100)) xs;
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
           (let uu____3138 = f x  in
            FStar_Util.string_builder_append strb uu____3138);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3145 = f x1  in
                 FStar_Util.string_builder_append strb uu____3145)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3161 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3161
  