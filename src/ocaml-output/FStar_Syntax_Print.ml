open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___95_5  ->
    match uu___95_5 with
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
  fun uu___96_281  ->
    match uu___96_281 with
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
         (fun uu___97_347  ->
            match uu___97_347 with
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
  fun uu___98_585  ->
    match uu___98_585 with
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
  fun uu___99_744  ->
    match uu___99_744 with
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
    | FStar_Syntax_Syntax.Tm_delayed (uu____1146,m) ->
        let uu____1188 = FStar_ST.op_Bang m  in
        (match uu____1188 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1248 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1253,m) ->
        let uu____1259 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1259
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1260 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1262 =
      let uu____1263 = FStar_Options.ugly ()  in Prims.op_Negation uu____1263
       in
    if uu____1262
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1271 = FStar_Options.print_implicits ()  in
         if uu____1271 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1275 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1300,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1320 =
             let uu____1321 =
               let uu____1330 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1330  in
             uu____1321 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1320
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1385;_})
           ->
           let uu____1400 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1400
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1402;_})
           ->
           let uu____1417 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1417
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1435 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1463 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1481  ->
                                 match uu____1481 with
                                 | (t1,uu____1487) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1463
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1435 (FStar_String.concat "\\/")  in
           let uu____1492 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1492
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1504 = tag_of_term t  in
           let uu____1505 = sli m  in
           let uu____1506 = term_to_string t'  in
           let uu____1507 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1504 uu____1505
             uu____1506 uu____1507
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1520 = tag_of_term t  in
           let uu____1521 = term_to_string t'  in
           let uu____1522 = sli m0  in
           let uu____1523 = sli m1  in
           let uu____1524 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1520
             uu____1521 uu____1522 uu____1523 uu____1524
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1533 = FStar_Range.string_of_range r  in
           let uu____1534 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1533
             uu____1534
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1541 = lid_to_string l  in
           let uu____1542 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1543 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1541 uu____1542
             uu____1543
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1545) ->
           let uu____1550 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1550
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1552 = db_to_string x3  in
           let uu____1553 =
             let uu____1554 =
               let uu____1555 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1555 ")"  in
             Prims.strcat ":(" uu____1554  in
           Prims.strcat uu____1552 uu____1553
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1559)) ->
           let uu____1580 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1580
           then ctx_uvar_to_string u
           else
             (let uu____1582 =
                let uu____1583 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1583  in
              Prims.strcat "?" uu____1582)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1606 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1606
           then
             let uu____1607 = ctx_uvar_to_string u  in
             let uu____1608 =
               let uu____1609 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1609 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1607 uu____1608
           else
             (let uu____1623 =
                let uu____1624 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1624  in
              Prims.strcat "?" uu____1623)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1627 = FStar_Options.print_universes ()  in
           if uu____1627
           then
             let uu____1628 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1628
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1648 = binders_to_string " -> " bs  in
           let uu____1649 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1648 uu____1649
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1674 = binders_to_string " " bs  in
                let uu____1675 = term_to_string t2  in
                let uu____1676 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1680 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1680)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1674 uu____1675
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1676
            | uu____1683 ->
                let uu____1686 = binders_to_string " " bs  in
                let uu____1687 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1686 uu____1687)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1694 = bv_to_string xt  in
           let uu____1695 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1696 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1694 uu____1695 uu____1696
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1721 = term_to_string t  in
           let uu____1722 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1721 uu____1722
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1741 = lbs_to_string [] lbs  in
           let uu____1742 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1741 uu____1742
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1803 =
                   let uu____1804 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1804
                     (FStar_Util.dflt "default")
                    in
                 let uu____1809 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1803 uu____1809
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1825 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1825
              in
           let uu____1826 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1826 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1865 = term_to_string head1  in
           let uu____1866 =
             let uu____1867 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1897  ->
                       match uu____1897 with
                       | (p,wopt,e) ->
                           let uu____1913 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1914 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1916 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1916
                              in
                           let uu____1917 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1913
                             uu____1914 uu____1917))
                in
             FStar_Util.concat_l "\n\t|" uu____1867  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1865 uu____1866
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1924 = FStar_Options.print_universes ()  in
           if uu____1924
           then
             let uu____1925 = term_to_string t  in
             let uu____1926 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1925 uu____1926
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1929 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1930 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1931 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1929 uu____1930
      uu____1931

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___100_1932  ->
    match uu___100_1932 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1935 = FStar_Util.string_of_int i  in
        let uu____1936 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1935 uu____1936
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1939 = bv_to_string x  in
        let uu____1940 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1939 uu____1940
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1947 = bv_to_string x  in
        let uu____1948 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____1947 uu____1948
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1951 = FStar_Util.string_of_int i  in
        let uu____1952 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1951 uu____1952
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1955 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1955

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1957 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1957 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1967 =
      let uu____1968 = FStar_Options.ugly ()  in Prims.op_Negation uu____1968
       in
    if uu____1967
    then
      let e =
        let uu____1970 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1970  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1993 = fv_to_string l  in
           let uu____1994 =
             let uu____1995 =
               FStar_List.map
                 (fun uu____2006  ->
                    match uu____2006 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1995 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1993 uu____1994
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2018) ->
           let uu____2023 = FStar_Options.print_bound_var_types ()  in
           if uu____2023
           then
             let uu____2024 = bv_to_string x1  in
             let uu____2025 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2024 uu____2025
           else
             (let uu____2027 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2027)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2029 = FStar_Options.print_bound_var_types ()  in
           if uu____2029
           then
             let uu____2030 = bv_to_string x1  in
             let uu____2031 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2030 uu____2031
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2035 = FStar_Options.print_real_names ()  in
           if uu____2035
           then
             let uu____2036 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2036
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2048 = quals_to_string' quals  in
      let uu____2049 =
        let uu____2050 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2066 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2067 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2068 =
                    let uu____2069 = FStar_Options.print_universes ()  in
                    if uu____2069
                    then
                      let uu____2070 =
                        let uu____2071 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2071 ">"  in
                      Prims.strcat "<" uu____2070
                    else ""  in
                  let uu____2073 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2074 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2066
                    uu____2067 uu____2068 uu____2073 uu____2074))
           in
        FStar_Util.concat_l "\n and " uu____2050  in
      FStar_Util.format3 "%slet %s %s" uu____2048
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2049

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___101_2078  ->
    match uu___101_2078 with
    | [] -> ""
    | tms ->
        let uu____2084 =
          let uu____2085 =
            FStar_List.map
              (fun t  ->
                 let uu____2091 = term_to_string t  in paren uu____2091) tms
             in
          FStar_All.pipe_right uu____2085 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2084

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2095 = FStar_Options.print_effect_args ()  in
    if uu____2095
    then
      let uu____2096 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2096
    else
      (let uu____2098 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2099 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2098 uu____2099)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___102_2100  ->
    match uu___102_2100 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2101 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2104 = aqual_to_string aq  in Prims.strcat uu____2104 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2111 =
        let uu____2112 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2112  in
      if uu____2111
      then
        let uu____2113 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2113 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2119 = b  in
         match uu____2119 with
         | (a,imp) ->
             let uu____2126 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2126
             then
               let uu____2127 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2127
             else
               (let uu____2129 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2131 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2131)
                   in
                if uu____2129
                then
                  let uu____2132 = nm_to_string a  in
                  imp_to_string uu____2132 imp
                else
                  (let uu____2134 =
                     let uu____2135 = nm_to_string a  in
                     let uu____2136 =
                       let uu____2137 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2137  in
                     Prims.strcat uu____2135 uu____2136  in
                   imp_to_string uu____2134 imp)))

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
        let uu____2153 = FStar_Options.print_implicits ()  in
        if uu____2153 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2161 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2161 (FStar_String.concat sep)
      else
        (let uu____2179 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2179 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___103_2188  ->
    match uu___103_2188 with
    | (a,imp) ->
        let uu____2195 = term_to_string a  in imp_to_string uu____2195 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2204 = FStar_Options.print_implicits ()  in
      if uu____2204 then args else filter_imp args  in
    let uu____2214 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2214 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2233 = FStar_Options.ugly ()  in
      if uu____2233
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2238 =
      let uu____2239 = FStar_Options.ugly ()  in Prims.op_Negation uu____2239
       in
    if uu____2238
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2253 =
             let uu____2254 = FStar_Syntax_Subst.compress t  in
             uu____2254.FStar_Syntax_Syntax.n  in
           (match uu____2253 with
            | FStar_Syntax_Syntax.Tm_type uu____2257 when
                let uu____2258 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2258 -> term_to_string t
            | uu____2259 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2261 = univ_to_string u  in
                     let uu____2262 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2261 uu____2262
                 | uu____2263 ->
                     let uu____2266 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2266))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2277 =
             let uu____2278 = FStar_Syntax_Subst.compress t  in
             uu____2278.FStar_Syntax_Syntax.n  in
           (match uu____2277 with
            | FStar_Syntax_Syntax.Tm_type uu____2281 when
                let uu____2282 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2282 -> term_to_string t
            | uu____2283 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2285 = univ_to_string u  in
                     let uu____2286 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2285 uu____2286
                 | uu____2287 ->
                     let uu____2290 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2290))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2293 = FStar_Options.print_effect_args ()  in
             if uu____2293
             then
               let uu____2294 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2295 =
                 let uu____2296 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2296 (FStar_String.concat ", ")
                  in
               let uu____2305 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2306 =
                 let uu____2307 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2307 (FStar_String.concat ", ")
                  in
               let uu____2324 =
                 let uu____2325 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2325 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2294
                 uu____2295 uu____2305 uu____2306 uu____2324
             else
               (let uu____2335 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___104_2339  ->
                           match uu___104_2339 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2340 -> false)))
                    &&
                    (let uu____2342 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2342)
                   in
                if uu____2335
                then
                  let uu____2343 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2343
                else
                  (let uu____2345 =
                     ((let uu____2348 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2348) &&
                        (let uu____2350 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2350))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2345
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2352 =
                        (let uu____2355 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2355) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___105_2359  ->
                                   match uu___105_2359 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2360 -> false)))
                         in
                      if uu____2352
                      then
                        let uu____2361 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2361
                      else
                        (let uu____2363 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2364 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2363 uu____2364))))
              in
           let dec =
             let uu____2366 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___106_2376  ->
                       match uu___106_2376 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2382 =
                             let uu____2383 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2383
                              in
                           [uu____2382]
                       | uu____2384 -> []))
                in
             FStar_All.pipe_right uu____2366 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2388 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___107_2394  ->
    match uu___107_2394 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2407 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2435 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2453  ->
                              match uu____2453 with
                              | (t,uu____2459) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2435
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2407 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2465 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2465
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2468) ->
        let uu____2469 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2469
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2477 = sli m  in
        let uu____2478 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2477 uu____2478
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2486 = sli m  in
        let uu____2487 = sli m'  in
        let uu____2488 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2486
          uu____2487 uu____2488

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2499 = FStar_Options.ugly ()  in
      if uu____2499
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
      let uu____2513 = b  in
      match uu____2513 with
      | (a,imp) ->
          let n1 =
            let uu____2517 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2517
            then FStar_Util.JsonNull
            else
              (let uu____2519 =
                 let uu____2520 = nm_to_string a  in
                 imp_to_string uu____2520 imp  in
               FStar_Util.JsonStr uu____2519)
             in
          let t =
            let uu____2522 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2522  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2545 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2545
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2557 = FStar_Options.print_universes ()  in
    if uu____2557 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2564 =
      let uu____2565 = FStar_Options.ugly ()  in Prims.op_Negation uu____2565
       in
    if uu____2564
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2569 = s  in
       match uu____2569 with
       | (us,t) ->
           let uu____2580 =
             let uu____2581 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2581  in
           let uu____2582 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2580 uu____2582)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2588 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2589 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2590 =
      let uu____2591 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2591  in
    let uu____2592 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2593 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2588 uu____2589 uu____2590
      uu____2592 uu____2593
  
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
          let uu____2618 =
            let uu____2619 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2619  in
          if uu____2618
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2633 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2633 (FStar_String.concat ",\n\t")
                in
             let uu____2642 =
               let uu____2645 =
                 let uu____2648 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2649 =
                   let uu____2652 =
                     let uu____2653 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2653  in
                   let uu____2654 =
                     let uu____2657 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2658 =
                       let uu____2661 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2662 =
                         let uu____2665 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2666 =
                           let uu____2669 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2670 =
                             let uu____2673 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2674 =
                               let uu____2677 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2678 =
                                 let uu____2681 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2682 =
                                   let uu____2685 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2686 =
                                     let uu____2689 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2690 =
                                       let uu____2693 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2694 =
                                         let uu____2697 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2698 =
                                           let uu____2701 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2702 =
                                             let uu____2705 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2706 =
                                               let uu____2709 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2710 =
                                                 let uu____2713 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2714 =
                                                   let uu____2717 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2717]  in
                                                 uu____2713 :: uu____2714  in
                                               uu____2709 :: uu____2710  in
                                             uu____2705 :: uu____2706  in
                                           uu____2701 :: uu____2702  in
                                         uu____2697 :: uu____2698  in
                                       uu____2693 :: uu____2694  in
                                     uu____2689 :: uu____2690  in
                                   uu____2685 :: uu____2686  in
                                 uu____2681 :: uu____2682  in
                               uu____2677 :: uu____2678  in
                             uu____2673 :: uu____2674  in
                           uu____2669 :: uu____2670  in
                         uu____2665 :: uu____2666  in
                       uu____2661 :: uu____2662  in
                     uu____2657 :: uu____2658  in
                   uu____2652 :: uu____2654  in
                 uu____2648 :: uu____2649  in
               (if for_free then "_for_free " else "") :: uu____2645  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2642)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2734 =
      let uu____2735 = FStar_Options.ugly ()  in Prims.op_Negation uu____2735
       in
    if uu____2734
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2741 -> ""
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
             (lid,univs1,tps,k,uu____2752,uu____2753) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2765 = FStar_Options.print_universes ()  in
             if uu____2765
             then
               let uu____2766 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2766 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2771,uu____2772,uu____2773) ->
             let uu____2778 = FStar_Options.print_universes ()  in
             if uu____2778
             then
               let uu____2779 = univ_names_to_string univs1  in
               let uu____2780 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2779
                 lid.FStar_Ident.str uu____2780
             else
               (let uu____2782 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2782)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2786 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2787 =
               let uu____2788 = FStar_Options.print_universes ()  in
               if uu____2788
               then
                 let uu____2789 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2789
               else ""  in
             let uu____2791 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2786
               lid.FStar_Ident.str uu____2787 uu____2791
         | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
             let uu____2795 = FStar_Options.print_universes ()  in
             if uu____2795
             then
               let uu____2796 = univ_names_to_string us  in
               let uu____2797 = term_to_string f  in
               FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
                 uu____2796 uu____2797
             else
               (let uu____2799 = term_to_string f  in
                FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str
                  uu____2799)
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2801) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2807 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2807
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2809) ->
             let uu____2818 =
               let uu____2819 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2819 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2818
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2849) -> lift_wp
               | (uu____2856,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2864 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2864 with
              | (us,t) ->
                  let uu____2871 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2872 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2873 = univ_names_to_string us  in
                  let uu____2874 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2871 uu____2872 uu____2873 uu____2874)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2884 = FStar_Options.print_universes ()  in
             if uu____2884
             then
               let uu____2885 =
                 let uu____2890 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2890  in
               (match uu____2885 with
                | (univs2,t) ->
                    let uu____2901 =
                      let uu____2914 =
                        let uu____2915 = FStar_Syntax_Subst.compress t  in
                        uu____2915.FStar_Syntax_Syntax.n  in
                      match uu____2914 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2956 -> failwith "impossible"  in
                    (match uu____2901 with
                     | (tps1,c1) ->
                         let uu____2987 = sli l  in
                         let uu____2988 = univ_names_to_string univs2  in
                         let uu____2989 = binders_to_string " " tps1  in
                         let uu____2990 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2987 uu____2988 uu____2989 uu____2990))
             else
               (let uu____2992 = sli l  in
                let uu____2993 = binders_to_string " " tps  in
                let uu____2994 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2992 uu____2993
                  uu____2994)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____3001 =
               let uu____3002 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____3002  in
             let uu____3007 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____3001 uu____3007
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____3008 ->
           let uu____3011 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____3011 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3022 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3022 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3028,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3030;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3032;
                       FStar_Syntax_Syntax.lbdef = uu____3033;
                       FStar_Syntax_Syntax.lbattrs = uu____3034;
                       FStar_Syntax_Syntax.lbpos = uu____3035;_}::[]),uu____3036)
        ->
        let uu____3057 = lbname_to_string lb  in
        let uu____3058 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3057 uu____3058
    | uu____3059 ->
        let uu____3060 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3060 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3076 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3077 =
      let uu____3078 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3078 (FStar_String.concat "\n")  in
    let uu____3083 =
      let uu____3084 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3084 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3076 uu____3077 uu____3083
  
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
          (let uu____3118 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3118))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3125 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3125)));
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
           (let uu____3159 = f x  in
            FStar_Util.string_builder_append strb uu____3159);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3166 = f x1  in
                 FStar_Util.string_builder_append strb uu____3166)) xs;
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
           (let uu____3204 = f x  in
            FStar_Util.string_builder_append strb uu____3204);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3211 = f x1  in
                 FStar_Util.string_builder_append strb uu____3211)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3227 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3227
  