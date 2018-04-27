open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___68_3  ->
    match uu___68_3 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____5 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_constant_at_level " uu____5
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____7 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_equational_at_level " uu____7
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____9 =
          let uu____10 = delta_depth_to_string d  in
          Prims.strcat uu____10 ")"  in
        Prims.strcat "Delta_abstract (" uu____9
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____14 = FStar_Options.print_real_names ()  in
    if uu____14
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    let uu____22 =
      lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
       in
    let uu____23 =
      let uu____24 =
        let uu____25 = delta_depth_to_string fv.FStar_Syntax_Syntax.fv_delta
           in
        Prims.strcat uu____25 ")"  in
      Prims.strcat "(@@" uu____24  in
    Prims.strcat uu____22 uu____23
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____29 =
      let uu____30 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____30  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____29
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____34 = FStar_Options.print_real_names ()  in
    if uu____34
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____39 =
      let uu____40 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____40  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____39
  
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
      | uu____174 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____183 -> failwith "get_lid"
  
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
  'Auu____238 'Auu____239 .
    ('Auu____238,'Auu____239) FStar_Util.either -> Prims.bool
  =
  fun uu___69_247  ->
    match uu___69_247 with
    | FStar_Util.Inl uu____252 -> false
    | FStar_Util.Inr uu____253 -> true
  
let filter_imp :
  'Auu____256 .
    ('Auu____256,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____256,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___70_310  ->
            match uu___70_310 with
            | (uu____317,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____318)) -> false
            | uu____321 -> true))
  
let rec (reconstruct_lex :
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____337 =
      let uu____338 = FStar_Syntax_Subst.compress e  in
      uu____338.FStar_Syntax_Syntax.n  in
    match uu____337 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____401 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____401
        then
          let uu____410 =
            let uu____417 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____417  in
          (match uu____410 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____435 =
                 let uu____440 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____440 :: xs  in
               FStar_Pervasives_Native.Some uu____435
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
          let uu____509 = f hd1  in if uu____509 then hd1 else find f tl1
  
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
  fun e  -> let uu____551 = get_lid e  in find_lid uu____551 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____559 = get_lid e  in find_lid uu____559 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____567 = get_lid t  in find_lid uu____567 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___71_573  ->
    match uu___71_573 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____579 = FStar_Options.hide_uvar_nums ()  in
    if uu____579
    then "?"
    else
      (let uu____581 =
         let uu____582 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____582 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____581)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____586 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____587 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____586 uu____587
  
let (univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string)
  =
  fun u  ->
    let uu____591 = FStar_Options.hide_uvar_nums ()  in
    if uu____591
    then "?"
    else
      (let uu____593 =
         let uu____594 =
           let uu____595 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____595 FStar_Util.string_of_int  in
         let uu____596 =
           let uu____597 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____597  in
         Prims.strcat uu____594 uu____596  in
       Prims.strcat "?" uu____593)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____614 = FStar_Syntax_Subst.compress_univ u  in
      match uu____614 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____624 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____630 =
      let uu____631 = FStar_Options.ugly ()  in Prims.op_Negation uu____631
       in
    if uu____630
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____635 = FStar_Syntax_Subst.compress_univ u  in
       match uu____635 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____647 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____647
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____649 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____649 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____663 = univ_to_string u2  in
                let uu____664 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____663 uu____664)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____668 =
             let uu____669 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____669 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____668
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____681 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____681 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____689 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____689 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___72_698  ->
    match uu___72_698 with
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
        let uu____700 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____700
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____703 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____703 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____714 =
          let uu____715 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____715  in
        let uu____716 =
          let uu____717 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____717 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____714 uu____716
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____736 =
          let uu____737 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____737  in
        let uu____738 =
          let uu____739 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____739 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____736 uu____738
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____749 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____749
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
    | uu____758 ->
        let uu____761 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____761 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____777 ->
        let uu____780 = quals_to_string quals  in Prims.strcat uu____780 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____850 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____850
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____852 = nm_to_string x  in Prims.strcat "Tm_name: " uu____852
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____854 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____854
    | FStar_Syntax_Syntax.Tm_uinst uu____855 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____862 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____863 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____864,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____865;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____880,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_dynamic ;
                     FStar_Syntax_Syntax.antiquotes = uu____881;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____896 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____913 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____926 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____933 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____948 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____971 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____998 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1011 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1028,m) ->
        let uu____1070 = FStar_ST.op_Bang m  in
        (match uu____1070 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1126 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1131,m) ->
        let uu____1137 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1137
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1138 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1140 =
      let uu____1141 = FStar_Options.ugly ()  in Prims.op_Negation uu____1141
       in
    if uu____1140
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1147 = FStar_Options.print_implicits ()  in
         if uu____1147 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1149 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1174,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1194 =
             let uu____1195 =
               let uu____1200 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1200  in
             uu____1195 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1194
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1243;_})
           ->
           let uu____1258 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1258
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1260;_})
           ->
           let uu____1275 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1275
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1293 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1323 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1341  ->
                                 match uu____1341 with
                                 | (t1,uu____1347) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1323
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1293 (FStar_String.concat "\\/")  in
           let uu____1352 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1352
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1364 = tag_of_term t  in
           let uu____1365 = sli m  in
           let uu____1366 = term_to_string t'  in
           let uu____1367 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1364 uu____1365
             uu____1366 uu____1367
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1380 = tag_of_term t  in
           let uu____1381 = term_to_string t'  in
           let uu____1382 = sli m0  in
           let uu____1383 = sli m1  in
           let uu____1384 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1380
             uu____1381 uu____1382 uu____1383 uu____1384
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1393 = FStar_Range.string_of_range r  in
           let uu____1394 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1393
             uu____1394
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1401 = lid_to_string l  in
           let uu____1402 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1403 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1401 uu____1402
             uu____1403
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1405) ->
           let uu____1410 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1410
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1412 = db_to_string x3  in
           let uu____1413 =
             let uu____1414 =
               let uu____1415 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1415 ")"  in
             Prims.strcat ":(" uu____1414  in
           Prims.strcat uu____1412 uu____1413
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1419) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1446 = FStar_Options.print_universes ()  in
           if uu____1446
           then
             let uu____1447 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1447
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1467 = binders_to_string " -> " bs  in
           let uu____1468 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1467 uu____1468
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1493 = binders_to_string " " bs  in
                let uu____1494 = term_to_string t2  in
                let uu____1495 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1499 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1499)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1493 uu____1494
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1495
            | uu____1502 ->
                let uu____1505 = binders_to_string " " bs  in
                let uu____1506 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1505 uu____1506)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1513 = bv_to_string xt  in
           let uu____1514 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1517 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1513 uu____1514 uu____1517
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1542 = term_to_string t  in
           let uu____1543 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1542 uu____1543
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1562 = lbs_to_string [] lbs  in
           let uu____1563 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1562 uu____1563
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1624 =
                   let uu____1625 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1625
                     (FStar_Util.dflt "default")
                    in
                 let uu____1630 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1624 uu____1630
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1646 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1646
              in
           let uu____1647 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1647 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1686 = term_to_string head1  in
           let uu____1687 =
             let uu____1688 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1724  ->
                       match uu____1724 with
                       | (p,wopt,e) ->
                           let uu____1740 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1741 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1743 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1743
                              in
                           let uu____1744 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1740
                             uu____1741 uu____1744))
                in
             FStar_Util.concat_l "\n\t|" uu____1688  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1686 uu____1687
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1751 = FStar_Options.print_universes ()  in
           if uu____1751
           then
             let uu____1752 = term_to_string t  in
             let uu____1753 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1752 uu____1753
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1756 =
      let uu____1757 = FStar_Options.ugly ()  in Prims.op_Negation uu____1757
       in
    if uu____1756
    then
      let e =
        let uu____1759 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1759  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1782 = fv_to_string l  in
           let uu____1783 =
             let uu____1784 =
               FStar_List.map
                 (fun uu____1795  ->
                    match uu____1795 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1784 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1782 uu____1783
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1807) ->
           let uu____1812 = FStar_Options.print_bound_var_types ()  in
           if uu____1812
           then
             let uu____1813 = bv_to_string x1  in
             let uu____1814 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1813 uu____1814
           else
             (let uu____1816 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1816)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1818 = FStar_Options.print_bound_var_types ()  in
           if uu____1818
           then
             let uu____1819 = bv_to_string x1  in
             let uu____1820 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1819 uu____1820
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1824 = FStar_Options.print_real_names ()  in
           if uu____1824
           then
             let uu____1825 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1825
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1837 = quals_to_string' quals  in
      let uu____1838 =
        let uu____1839 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1855 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1856 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1857 =
                    let uu____1858 = FStar_Options.print_universes ()  in
                    if uu____1858
                    then
                      let uu____1859 =
                        let uu____1860 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1860 ">"  in
                      Prims.strcat "<" uu____1859
                    else ""  in
                  let uu____1862 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1863 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1855
                    uu____1856 uu____1857 uu____1862 uu____1863))
           in
        FStar_Util.concat_l "\n and " uu____1839  in
      FStar_Util.format3 "%slet %s %s" uu____1837
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1838

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___73_1869  ->
    match uu___73_1869 with
    | [] -> ""
    | tms ->
        let uu____1875 =
          let uu____1876 =
            FStar_List.map
              (fun t  ->
                 let uu____1882 = term_to_string t  in paren uu____1882) tms
             in
          FStar_All.pipe_right uu____1876 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1875

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1886 = FStar_Options.print_effect_args ()  in
    if uu____1886
    then
      let uu____1887 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1887
    else
      (let uu____1889 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1890 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1889 uu____1890)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___74_1891  ->
    match uu___74_1891 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1892 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1895 = aqual_to_string aq  in Prims.strcat uu____1895 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____1898 =
        let uu____1899 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1899  in
      if uu____1898
      then
        let uu____1900 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1900 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1906 = b  in
         match uu____1906 with
         | (a,imp) ->
             let uu____1909 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1909
             then
               let uu____1910 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1910
             else
               (let uu____1912 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1914 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1914)
                   in
                if uu____1912
                then
                  let uu____1915 = nm_to_string a  in
                  imp_to_string uu____1915 imp
                else
                  (let uu____1917 =
                     let uu____1918 = nm_to_string a  in
                     let uu____1919 =
                       let uu____1920 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1920  in
                     Prims.strcat uu____1918 uu____1919  in
                   imp_to_string uu____1917 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1926 = FStar_Options.print_implicits ()  in
        if uu____1926 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1928 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1928 (FStar_String.concat sep)
      else
        (let uu____1936 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1936 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___75_1943  ->
    match uu___75_1943 with
    | (a,imp) ->
        let uu____1950 = term_to_string a  in imp_to_string uu____1950 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____1953 = FStar_Options.print_implicits ()  in
      if uu____1953 then args else filter_imp args  in
    let uu____1957 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1957 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____1970 = FStar_Options.ugly ()  in
      if uu____1970
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____1975 =
      let uu____1976 = FStar_Options.ugly ()  in Prims.op_Negation uu____1976
       in
    if uu____1975
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1990 =
             let uu____1991 = FStar_Syntax_Subst.compress t  in
             uu____1991.FStar_Syntax_Syntax.n  in
           (match uu____1990 with
            | FStar_Syntax_Syntax.Tm_type uu____1994 when
                let uu____1995 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1995 -> term_to_string t
            | uu____1996 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1998 = univ_to_string u  in
                     let uu____1999 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____1998 uu____1999
                 | uu____2000 ->
                     let uu____2003 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2003))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2014 =
             let uu____2015 = FStar_Syntax_Subst.compress t  in
             uu____2015.FStar_Syntax_Syntax.n  in
           (match uu____2014 with
            | FStar_Syntax_Syntax.Tm_type uu____2018 when
                let uu____2019 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2019 -> term_to_string t
            | uu____2020 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2022 = univ_to_string u  in
                     let uu____2023 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2022 uu____2023
                 | uu____2024 ->
                     let uu____2027 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2027))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2030 = FStar_Options.print_effect_args ()  in
             if uu____2030
             then
               let uu____2031 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2032 =
                 let uu____2033 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2033 (FStar_String.concat ", ")
                  in
               let uu____2040 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2041 =
                 let uu____2042 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2042 (FStar_String.concat ", ")
                  in
               let uu____2061 =
                 let uu____2062 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2062 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2031
                 uu____2032 uu____2040 uu____2041 uu____2061
             else
               (let uu____2072 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___76_2076  ->
                           match uu___76_2076 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2077 -> false)))
                    &&
                    (let uu____2079 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2079)
                   in
                if uu____2072
                then
                  let uu____2080 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2080
                else
                  (let uu____2082 =
                     ((let uu____2085 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2085) &&
                        (let uu____2087 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2087))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2082
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2089 =
                        (let uu____2092 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2092) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___77_2096  ->
                                   match uu___77_2096 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2097 -> false)))
                         in
                      if uu____2089
                      then
                        let uu____2098 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2098
                      else
                        (let uu____2100 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2101 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2100 uu____2101))))
              in
           let dec =
             let uu____2103 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___78_2113  ->
                       match uu___78_2113 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2119 =
                             let uu____2120 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2120
                              in
                           [uu____2119]
                       | uu____2121 -> []))
                in
             FStar_All.pipe_right uu____2103 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2125 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___79_2131  ->
    match uu___79_2131 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2144 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2174 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2192  ->
                              match uu____2192 with
                              | (t,uu____2198) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2174
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2144 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2204 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2204
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2207) ->
        let uu____2208 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2208
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2216 = sli m  in
        let uu____2217 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2216 uu____2217
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2225 = sli m  in
        let uu____2226 = sli m'  in
        let uu____2227 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2225
          uu____2226 uu____2227

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2234 = FStar_Options.ugly ()  in
      if uu____2234
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
      let uu____2244 = b  in
      match uu____2244 with
      | (a,imp) ->
          let n1 =
            let uu____2248 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2248
            then FStar_Util.JsonNull
            else
              (let uu____2250 =
                 let uu____2251 = nm_to_string a  in
                 imp_to_string uu____2251 imp  in
               FStar_Util.JsonStr uu____2250)
             in
          let t =
            let uu____2253 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2253  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2272 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2272
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2278 = FStar_Options.print_universes ()  in
    if uu____2278 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2283 =
      let uu____2284 = FStar_Options.ugly ()  in Prims.op_Negation uu____2284
       in
    if uu____2283
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2288 = s  in
       match uu____2288 with
       | (us,t) ->
           let uu____2295 =
             let uu____2296 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2296  in
           let uu____2297 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2295 uu____2297)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2301 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2302 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2303 =
      let uu____2304 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2304  in
    let uu____2305 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2306 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2301 uu____2302 uu____2303
      uu____2305 uu____2306
  
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
          let uu____2323 =
            let uu____2324 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2324  in
          if uu____2323
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2336 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2336 (FStar_String.concat ",\n\t")
                in
             let uu____2345 =
               let uu____2348 =
                 let uu____2351 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2352 =
                   let uu____2355 =
                     let uu____2356 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2356  in
                   let uu____2357 =
                     let uu____2360 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2361 =
                       let uu____2364 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2365 =
                         let uu____2368 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2369 =
                           let uu____2372 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2373 =
                             let uu____2376 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2377 =
                               let uu____2380 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2381 =
                                 let uu____2384 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2385 =
                                   let uu____2388 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2389 =
                                     let uu____2392 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2393 =
                                       let uu____2396 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2397 =
                                         let uu____2400 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2401 =
                                           let uu____2404 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2405 =
                                             let uu____2408 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2409 =
                                               let uu____2412 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2413 =
                                                 let uu____2416 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2417 =
                                                   let uu____2420 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2420]  in
                                                 uu____2416 :: uu____2417  in
                                               uu____2412 :: uu____2413  in
                                             uu____2408 :: uu____2409  in
                                           uu____2404 :: uu____2405  in
                                         uu____2400 :: uu____2401  in
                                       uu____2396 :: uu____2397  in
                                     uu____2392 :: uu____2393  in
                                   uu____2388 :: uu____2389  in
                                 uu____2384 :: uu____2385  in
                               uu____2380 :: uu____2381  in
                             uu____2376 :: uu____2377  in
                           uu____2372 :: uu____2373  in
                         uu____2368 :: uu____2369  in
                       uu____2364 :: uu____2365  in
                     uu____2360 :: uu____2361  in
                   uu____2355 :: uu____2357  in
                 uu____2351 :: uu____2352  in
               (if for_free then "_for_free " else "") :: uu____2348  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2345)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2431 =
      let uu____2432 = FStar_Options.ugly ()  in Prims.op_Negation uu____2432
       in
    if uu____2431
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2438 -> ""
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
             (lid,univs1,tps,k,uu____2449,uu____2450) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2462 = FStar_Options.print_universes ()  in
             if uu____2462
             then
               let uu____2463 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2463 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2468,uu____2469,uu____2470) ->
             let uu____2475 = FStar_Options.print_universes ()  in
             if uu____2475
             then
               let uu____2476 = univ_names_to_string univs1  in
               let uu____2477 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2476
                 lid.FStar_Ident.str uu____2477
             else
               (let uu____2479 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2479)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2483 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2484 =
               let uu____2485 = FStar_Options.print_universes ()  in
               if uu____2485
               then
                 let uu____2486 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2486
               else ""  in
             let uu____2488 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2483
               lid.FStar_Ident.str uu____2484 uu____2488
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2490,f) ->
             let uu____2492 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2492
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2494) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2500 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2500
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2502) ->
             let uu____2511 =
               let uu____2512 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2512 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2511
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2530) -> lift_wp
               | (uu____2537,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2545 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2545 with
              | (us,t) ->
                  let uu____2556 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2557 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2558 = univ_names_to_string us  in
                  let uu____2559 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2556 uu____2557 uu____2558 uu____2559)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2569 = FStar_Options.print_universes ()  in
             if uu____2569
             then
               let uu____2570 =
                 let uu____2575 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2575  in
               (match uu____2570 with
                | (univs2,t) ->
                    let uu____2578 =
                      let uu____2591 =
                        let uu____2592 = FStar_Syntax_Subst.compress t  in
                        uu____2592.FStar_Syntax_Syntax.n  in
                      match uu____2591 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2633 -> failwith "impossible"  in
                    (match uu____2578 with
                     | (tps1,c1) ->
                         let uu____2664 = sli l  in
                         let uu____2665 = univ_names_to_string univs2  in
                         let uu____2666 = binders_to_string " " tps1  in
                         let uu____2667 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2664 uu____2665 uu____2666 uu____2667))
             else
               (let uu____2669 = sli l  in
                let uu____2670 = binders_to_string " " tps  in
                let uu____2671 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2669 uu____2670
                  uu____2671)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2678 =
               let uu____2679 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2679  in
             let uu____2684 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2678 uu____2684
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2685 ->
           let uu____2688 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2688 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2695 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2695 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2699,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2701;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2703;
                       FStar_Syntax_Syntax.lbdef = uu____2704;
                       FStar_Syntax_Syntax.lbattrs = uu____2705;
                       FStar_Syntax_Syntax.lbpos = uu____2706;_}::[]),uu____2707)
        ->
        let uu____2734 = lbname_to_string lb  in
        let uu____2735 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2734 uu____2735
    | uu____2736 ->
        let uu____2737 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2737 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2751 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2752 =
      let uu____2753 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2753 (FStar_String.concat "\n")  in
    let uu____2758 =
      let uu____2759 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2759 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2751 uu____2752 uu____2758
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___80_2766  ->
    match uu___80_2766 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2769 = FStar_Util.string_of_int i  in
        let uu____2770 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2769 uu____2770
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2773 = bv_to_string x  in
        let uu____2774 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2773 uu____2774
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2781 = bv_to_string x  in
        let uu____2782 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2781 uu____2782
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2785 = FStar_Util.string_of_int i  in
        let uu____2786 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2785 uu____2786
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2789 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2789
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2793 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2793 (FStar_String.concat "; ")
  
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
          (let uu____2827 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____2827))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____2834 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____2834)));
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
           (let uu____2863 = f x  in
            FStar_Util.string_builder_append strb uu____2863);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2870 = f x1  in
                 FStar_Util.string_builder_append strb uu____2870)) xs;
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
           (let uu____2903 = f x  in
            FStar_Util.string_builder_append strb uu____2903);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2910 = f x1  in
                 FStar_Util.string_builder_append strb uu____2910)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____2922 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____2922
  