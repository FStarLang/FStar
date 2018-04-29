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
          let uu____435 =
            let uu____440 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____440  in
          (match uu____435 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____450 =
                 let uu____453 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____453 :: xs  in
               FStar_Pervasives_Native.Some uu____450
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____463 ->
        let uu____464 = is_lex_top e  in
        if uu____464
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____505 = f hd1  in if uu____505 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____529 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____529
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____553 = get_lid e  in find_lid uu____553 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____563 = get_lid e  in find_lid uu____563 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____573 = get_lid t  in find_lid uu____573 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___71_583  ->
    match uu___71_583 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____591 = FStar_Options.hide_uvar_nums ()  in
    if uu____591
    then "?"
    else
      (let uu____593 =
         let uu____594 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____594 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____593)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____600 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____601 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____600 uu____601
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
     FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun u  ->
    let uu____623 = FStar_Options.hide_uvar_nums ()  in
    if uu____623
    then "?"
    else
      (let uu____625 =
         let uu____626 =
           let uu____627 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____627 FStar_Util.string_of_int  in
         let uu____628 =
           let uu____629 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____629  in
         Prims.strcat uu____626 uu____628  in
       Prims.strcat "?" uu____625)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____650 = FStar_Syntax_Subst.compress_univ u  in
      match uu____650 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____660 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____668 =
      let uu____669 = FStar_Options.ugly ()  in Prims.op_Negation uu____669
       in
    if uu____668
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____673 = FStar_Syntax_Subst.compress_univ u  in
       match uu____673 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____685 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____685
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____687 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____687 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____701 = univ_to_string u2  in
                let uu____702 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____701 uu____702)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____706 =
             let uu____707 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____707 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____706
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____721 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____721 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____731 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____731 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___72_742  ->
    match uu___72_742 with
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
        let uu____744 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____744
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____747 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____747 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____758 =
          let uu____759 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____759  in
        let uu____760 =
          let uu____761 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____761 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____758 uu____760
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____780 =
          let uu____781 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____781  in
        let uu____782 =
          let uu____783 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____783 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____780 uu____782
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____793 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____793
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
    | uu____804 ->
        let uu____807 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____807 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____825 ->
        let uu____828 = quals_to_string quals  in Prims.strcat uu____828 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____956 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____956
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____958 = nm_to_string x  in Prims.strcat "Tm_name: " uu____958
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____960 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____960
    | FStar_Syntax_Syntax.Tm_uinst uu____961 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____968 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____969 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____970,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____971;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____986,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_dynamic ;
                     FStar_Syntax_Syntax.antiquotes = uu____987;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1002 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1019 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1032 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1039 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1054 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1077 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1104 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1117 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1118,m) ->
        let uu____1160 = FStar_ST.op_Bang m  in
        (match uu____1160 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1220 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1225,m) ->
        let uu____1231 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1231
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1232 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1234 =
      let uu____1235 = FStar_Options.ugly ()  in Prims.op_Negation uu____1235
       in
    if uu____1234
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1243 = FStar_Options.print_implicits ()  in
         if uu____1243 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1247 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1272,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1292 =
             let uu____1293 =
               let uu____1302 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1302  in
             uu____1293 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1292
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1357;_})
           ->
           let uu____1372 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1372
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1374;_})
           ->
           let uu____1389 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1389
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1407 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1435 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1453  ->
                                 match uu____1453 with
                                 | (t1,uu____1459) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1435
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1407 (FStar_String.concat "\\/")  in
           let uu____1464 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1464
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1476 = tag_of_term t  in
           let uu____1477 = sli m  in
           let uu____1478 = term_to_string t'  in
           let uu____1479 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1476 uu____1477
             uu____1478 uu____1479
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1492 = tag_of_term t  in
           let uu____1493 = term_to_string t'  in
           let uu____1494 = sli m0  in
           let uu____1495 = sli m1  in
           let uu____1496 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1492
             uu____1493 uu____1494 uu____1495 uu____1496
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1505 = FStar_Range.string_of_range r  in
           let uu____1506 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1505
             uu____1506
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1513 = lid_to_string l  in
           let uu____1514 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1515 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1513 uu____1514
             uu____1515
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1517) ->
           let uu____1522 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1522
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1524 = db_to_string x3  in
           let uu____1525 =
             let uu____1526 =
               let uu____1527 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1527 ")"  in
             Prims.strcat ":(" uu____1526  in
           Prims.strcat uu____1524 uu____1525
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar u ->
           uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1533 = FStar_Options.print_universes ()  in
           if uu____1533
           then
             let uu____1534 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1534
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1554 = binders_to_string " -> " bs  in
           let uu____1555 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1554 uu____1555
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1580 = binders_to_string " " bs  in
                let uu____1581 = term_to_string t2  in
                let uu____1582 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1586 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1586)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1580 uu____1581
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1582
            | uu____1589 ->
                let uu____1592 = binders_to_string " " bs  in
                let uu____1593 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1592 uu____1593)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1600 = bv_to_string xt  in
           let uu____1601 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1602 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1600 uu____1601 uu____1602
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1627 = term_to_string t  in
           let uu____1628 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1627 uu____1628
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1647 = lbs_to_string [] lbs  in
           let uu____1648 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1647 uu____1648
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1709 =
                   let uu____1710 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1710
                     (FStar_Util.dflt "default")
                    in
                 let uu____1715 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1709 uu____1715
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1731 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1731
              in
           let uu____1732 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1732 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1771 = term_to_string head1  in
           let uu____1772 =
             let uu____1773 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1803  ->
                       match uu____1803 with
                       | (p,wopt,e) ->
                           let uu____1819 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1820 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1822 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1822
                              in
                           let uu____1823 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1819
                             uu____1820 uu____1823))
                in
             FStar_Util.concat_l "\n\t|" uu____1773  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1771 uu____1772
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1830 = FStar_Options.print_universes ()  in
           if uu____1830
           then
             let uu____1831 = term_to_string t  in
             let uu____1832 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1831 uu____1832
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1835 =
      let uu____1836 = FStar_Options.ugly ()  in Prims.op_Negation uu____1836
       in
    if uu____1835
    then
      let e =
        let uu____1838 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1838  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1861 = fv_to_string l  in
           let uu____1862 =
             let uu____1863 =
               FStar_List.map
                 (fun uu____1874  ->
                    match uu____1874 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1863 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1861 uu____1862
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1886) ->
           let uu____1891 = FStar_Options.print_bound_var_types ()  in
           if uu____1891
           then
             let uu____1892 = bv_to_string x1  in
             let uu____1893 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1892 uu____1893
           else
             (let uu____1895 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1895)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1897 = FStar_Options.print_bound_var_types ()  in
           if uu____1897
           then
             let uu____1898 = bv_to_string x1  in
             let uu____1899 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1898 uu____1899
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1903 = FStar_Options.print_real_names ()  in
           if uu____1903
           then
             let uu____1904 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1904
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1916 = quals_to_string' quals  in
      let uu____1917 =
        let uu____1918 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1934 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1935 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1936 =
                    let uu____1937 = FStar_Options.print_universes ()  in
                    if uu____1937
                    then
                      let uu____1938 =
                        let uu____1939 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1939 ">"  in
                      Prims.strcat "<" uu____1938
                    else ""  in
                  let uu____1941 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1942 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1934
                    uu____1935 uu____1936 uu____1941 uu____1942))
           in
        FStar_Util.concat_l "\n and " uu____1918  in
      FStar_Util.format3 "%slet %s %s" uu____1916
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1917

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___73_1946  ->
    match uu___73_1946 with
    | [] -> ""
    | tms ->
        let uu____1952 =
          let uu____1953 =
            FStar_List.map
              (fun t  ->
                 let uu____1959 = term_to_string t  in paren uu____1959) tms
             in
          FStar_All.pipe_right uu____1953 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1952

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1963 = FStar_Options.print_effect_args ()  in
    if uu____1963
    then
      let uu____1964 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1964
    else
      (let uu____1966 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1967 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1966 uu____1967)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___74_1968  ->
    match uu___74_1968 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1969 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1972 = aqual_to_string aq  in Prims.strcat uu____1972 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____1979 =
        let uu____1980 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1980  in
      if uu____1979
      then
        let uu____1981 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1981 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1987 = b  in
         match uu____1987 with
         | (a,imp) ->
             let uu____1994 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1994
             then
               let uu____1995 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1995
             else
               (let uu____1997 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1999 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1999)
                   in
                if uu____1997
                then
                  let uu____2000 = nm_to_string a  in
                  imp_to_string uu____2000 imp
                else
                  (let uu____2002 =
                     let uu____2003 = nm_to_string a  in
                     let uu____2004 =
                       let uu____2005 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2005  in
                     Prims.strcat uu____2003 uu____2004  in
                   imp_to_string uu____2002 imp)))

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
        let uu____2017 = FStar_Options.print_implicits ()  in
        if uu____2017 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2021 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2021 (FStar_String.concat sep)
      else
        (let uu____2039 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2039 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___75_2048  ->
    match uu___75_2048 with
    | (a,imp) ->
        let uu____2055 = term_to_string a  in imp_to_string uu____2055 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2064 = FStar_Options.print_implicits ()  in
      if uu____2064 then args else filter_imp args  in
    let uu____2074 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2074 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2093 = FStar_Options.ugly ()  in
      if uu____2093
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2098 =
      let uu____2099 = FStar_Options.ugly ()  in Prims.op_Negation uu____2099
       in
    if uu____2098
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2113 =
             let uu____2114 = FStar_Syntax_Subst.compress t  in
             uu____2114.FStar_Syntax_Syntax.n  in
           (match uu____2113 with
            | FStar_Syntax_Syntax.Tm_type uu____2117 when
                let uu____2118 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2118 -> term_to_string t
            | uu____2119 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2121 = univ_to_string u  in
                     let uu____2122 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2121 uu____2122
                 | uu____2123 ->
                     let uu____2126 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2126))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2137 =
             let uu____2138 = FStar_Syntax_Subst.compress t  in
             uu____2138.FStar_Syntax_Syntax.n  in
           (match uu____2137 with
            | FStar_Syntax_Syntax.Tm_type uu____2141 when
                let uu____2142 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2142 -> term_to_string t
            | uu____2143 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2145 = univ_to_string u  in
                     let uu____2146 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2145 uu____2146
                 | uu____2147 ->
                     let uu____2150 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2150))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2153 = FStar_Options.print_effect_args ()  in
             if uu____2153
             then
               let uu____2154 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2155 =
                 let uu____2156 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2156 (FStar_String.concat ", ")
                  in
               let uu____2165 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2166 =
                 let uu____2167 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2167 (FStar_String.concat ", ")
                  in
               let uu____2184 =
                 let uu____2185 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2185 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2154
                 uu____2155 uu____2165 uu____2166 uu____2184
             else
               (let uu____2195 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___76_2199  ->
                           match uu___76_2199 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2200 -> false)))
                    &&
                    (let uu____2202 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2202)
                   in
                if uu____2195
                then
                  let uu____2203 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2203
                else
                  (let uu____2205 =
                     ((let uu____2208 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2208) &&
                        (let uu____2210 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2210))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2205
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2212 =
                        (let uu____2215 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2215) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___77_2219  ->
                                   match uu___77_2219 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2220 -> false)))
                         in
                      if uu____2212
                      then
                        let uu____2221 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2221
                      else
                        (let uu____2223 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2224 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2223 uu____2224))))
              in
           let dec =
             let uu____2226 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___78_2236  ->
                       match uu___78_2236 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2242 =
                             let uu____2243 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2243
                              in
                           [uu____2242]
                       | uu____2244 -> []))
                in
             FStar_All.pipe_right uu____2226 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2248 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___79_2254  ->
    match uu___79_2254 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2267 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2295 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2313  ->
                              match uu____2313 with
                              | (t,uu____2319) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2295
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2267 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2325 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2325
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2328) ->
        let uu____2329 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2329
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2337 = sli m  in
        let uu____2338 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2337 uu____2338
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2346 = sli m  in
        let uu____2347 = sli m'  in
        let uu____2348 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2346
          uu____2347 uu____2348

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2359 = FStar_Options.ugly ()  in
      if uu____2359
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
      let uu____2373 = b  in
      match uu____2373 with
      | (a,imp) ->
          let n1 =
            let uu____2377 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2377
            then FStar_Util.JsonNull
            else
              (let uu____2379 =
                 let uu____2380 = nm_to_string a  in
                 imp_to_string uu____2380 imp  in
               FStar_Util.JsonStr uu____2379)
             in
          let t =
            let uu____2382 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2382  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2405 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2405
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2417 = FStar_Options.print_universes ()  in
    if uu____2417 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2424 =
      let uu____2425 = FStar_Options.ugly ()  in Prims.op_Negation uu____2425
       in
    if uu____2424
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2429 = s  in
       match uu____2429 with
       | (us,t) ->
           let uu____2440 =
             let uu____2441 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2441  in
           let uu____2442 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2440 uu____2442)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2448 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2449 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2450 =
      let uu____2451 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2451  in
    let uu____2452 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2453 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2448 uu____2449 uu____2450
      uu____2452 uu____2453
  
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
          let uu____2478 =
            let uu____2479 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2479  in
          if uu____2478
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2493 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2493 (FStar_String.concat ",\n\t")
                in
             let uu____2502 =
               let uu____2505 =
                 let uu____2508 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2509 =
                   let uu____2512 =
                     let uu____2513 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2513  in
                   let uu____2514 =
                     let uu____2517 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2518 =
                       let uu____2521 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2522 =
                         let uu____2525 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2526 =
                           let uu____2529 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2530 =
                             let uu____2533 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2534 =
                               let uu____2537 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2538 =
                                 let uu____2541 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2542 =
                                   let uu____2545 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2546 =
                                     let uu____2549 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2550 =
                                       let uu____2553 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2554 =
                                         let uu____2557 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2558 =
                                           let uu____2561 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2562 =
                                             let uu____2565 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2566 =
                                               let uu____2569 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2570 =
                                                 let uu____2573 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2574 =
                                                   let uu____2577 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2577]  in
                                                 uu____2573 :: uu____2574  in
                                               uu____2569 :: uu____2570  in
                                             uu____2565 :: uu____2566  in
                                           uu____2561 :: uu____2562  in
                                         uu____2557 :: uu____2558  in
                                       uu____2553 :: uu____2554  in
                                     uu____2549 :: uu____2550  in
                                   uu____2545 :: uu____2546  in
                                 uu____2541 :: uu____2542  in
                               uu____2537 :: uu____2538  in
                             uu____2533 :: uu____2534  in
                           uu____2529 :: uu____2530  in
                         uu____2525 :: uu____2526  in
                       uu____2521 :: uu____2522  in
                     uu____2517 :: uu____2518  in
                   uu____2512 :: uu____2514  in
                 uu____2508 :: uu____2509  in
               (if for_free then "_for_free " else "") :: uu____2505  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2502)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2594 =
      let uu____2595 = FStar_Options.ugly ()  in Prims.op_Negation uu____2595
       in
    if uu____2594
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2601 -> ""
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
             (lid,univs1,tps,k,uu____2612,uu____2613) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2625 = FStar_Options.print_universes ()  in
             if uu____2625
             then
               let uu____2626 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2626 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2631,uu____2632,uu____2633) ->
             let uu____2638 = FStar_Options.print_universes ()  in
             if uu____2638
             then
               let uu____2639 = univ_names_to_string univs1  in
               let uu____2640 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2639
                 lid.FStar_Ident.str uu____2640
             else
               (let uu____2642 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2642)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2646 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2647 =
               let uu____2648 = FStar_Options.print_universes ()  in
               if uu____2648
               then
                 let uu____2649 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2649
               else ""  in
             let uu____2651 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2646
               lid.FStar_Ident.str uu____2647 uu____2651
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2653,f) ->
             let uu____2655 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2655
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2657) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2663 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2663
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2665) ->
             let uu____2674 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2674 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2704) -> lift_wp
               | (uu____2711,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2719 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2719 with
              | (us,t) ->
                  let uu____2726 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2727 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2728 = univ_names_to_string us  in
                  let uu____2729 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2726 uu____2727 uu____2728 uu____2729)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2739 = FStar_Options.print_universes ()  in
             if uu____2739
             then
               let uu____2740 =
                 let uu____2745 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2745  in
               (match uu____2740 with
                | (univs2,t) ->
                    let uu____2756 =
                      let uu____2769 =
                        let uu____2770 = FStar_Syntax_Subst.compress t  in
                        uu____2770.FStar_Syntax_Syntax.n  in
                      match uu____2769 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2811 -> failwith "impossible"  in
                    (match uu____2756 with
                     | (tps1,c1) ->
                         let uu____2842 = sli l  in
                         let uu____2843 = univ_names_to_string univs2  in
                         let uu____2844 = binders_to_string " " tps1  in
                         let uu____2845 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2842 uu____2843 uu____2844 uu____2845))
             else
               (let uu____2847 = sli l  in
                let uu____2848 = binders_to_string " " tps  in
                let uu____2849 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2847 uu____2848
                  uu____2849)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2856 =
               let uu____2857 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2857  in
             let uu____2862 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2856 uu____2862
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2863 ->
           let uu____2866 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2866 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2877 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2877 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2883,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2885;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2887;
                       FStar_Syntax_Syntax.lbdef = uu____2888;
                       FStar_Syntax_Syntax.lbattrs = uu____2889;
                       FStar_Syntax_Syntax.lbpos = uu____2890;_}::[]),uu____2891)
        ->
        let uu____2912 = lbname_to_string lb  in
        let uu____2913 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2912 uu____2913
    | uu____2914 ->
        let uu____2915 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2915 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2931 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2932 =
      let uu____2933 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2933 (FStar_String.concat "\n")  in
    let uu____2938 =
      let uu____2939 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2939 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2931 uu____2932 uu____2938
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___80_2948  ->
    match uu___80_2948 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2951 = FStar_Util.string_of_int i  in
        let uu____2952 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2951 uu____2952
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2955 = bv_to_string x  in
        let uu____2956 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2955 uu____2956
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2963 = bv_to_string x  in
        let uu____2964 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2963 uu____2964
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2967 = FStar_Util.string_of_int i  in
        let uu____2968 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2967 uu____2968
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2971 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2971
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2977 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2977 (FStar_String.concat "; ")
  
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
          (let uu____3015 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3015))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3022 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3022)));
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
           (let uu____3056 = f x  in
            FStar_Util.string_builder_append strb uu____3056);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3063 = f x1  in
                 FStar_Util.string_builder_append strb uu____3063)) xs;
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
           (let uu____3101 = f x  in
            FStar_Util.string_builder_append strb uu____3101);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3108 = f x1  in
                 FStar_Util.string_builder_append strb uu____3108)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3124 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3124
  
let (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____3134 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____3135 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____3136 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format3 "(%s |- %s : %s)" uu____3134 uu____3135 uu____3136
  