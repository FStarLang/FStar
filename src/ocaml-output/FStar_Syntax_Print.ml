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
        let uu____428 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____428
        then
          let uu____433 =
            let uu____438 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____438  in
          (match uu____433 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____448 =
                 let uu____451 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____451 :: xs  in
               FStar_Pervasives_Native.Some uu____448
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____461 ->
        let uu____462 = is_lex_top e  in
        if uu____462
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____503 = f hd1  in if uu____503 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____527 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____527
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____551 = get_lid e  in find_lid uu____551 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____561 = get_lid e  in find_lid uu____561 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____571 = get_lid t  in find_lid uu____571 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___71_581  ->
    match uu___71_581 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____589 = FStar_Options.hide_uvar_nums ()  in
    if uu____589
    then "?"
    else
      (let uu____591 =
         let uu____592 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____592 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____591)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____598 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____599 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____598 uu____599
  
let (univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string)
  =
  fun u  ->
    let uu____605 = FStar_Options.hide_uvar_nums ()  in
    if uu____605
    then "?"
    else
      (let uu____607 =
         let uu____608 =
           let uu____609 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____609 FStar_Util.string_of_int  in
         let uu____610 =
           let uu____611 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____611  in
         Prims.strcat uu____608 uu____610  in
       Prims.strcat "?" uu____607)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____632 = FStar_Syntax_Subst.compress_univ u  in
      match uu____632 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____642 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____650 =
      let uu____651 = FStar_Options.ugly ()  in Prims.op_Negation uu____651
       in
    if uu____650
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____655 = FStar_Syntax_Subst.compress_univ u  in
       match uu____655 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____667 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____667
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____669 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____669 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____683 = univ_to_string u2  in
                let uu____684 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____683 uu____684)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____688 =
             let uu____689 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____689 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____688
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____703 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____703 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____713 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____713 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___72_724  ->
    match uu___72_724 with
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
        let uu____726 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____726
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____729 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____729 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____740 =
          let uu____741 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____741  in
        let uu____742 =
          let uu____743 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____743 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____740 uu____742
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____762 =
          let uu____763 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____763  in
        let uu____764 =
          let uu____765 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____765 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____762 uu____764
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____775 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____775
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
    | uu____786 ->
        let uu____789 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____789 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____807 ->
        let uu____810 = quals_to_string quals  in Prims.strcat uu____810 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____938 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____938
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____940 = nm_to_string x  in Prims.strcat "Tm_name: " uu____940
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____942 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____942
    | FStar_Syntax_Syntax.Tm_uinst uu____943 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____950 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____951 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____952,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____953;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____968,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_dynamic ;
                     FStar_Syntax_Syntax.antiquotes = uu____969;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____984 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1001 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1014 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1021 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1036 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1059 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1086 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1099 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1100,m) ->
        let uu____1142 = FStar_ST.op_Bang m  in
        (match uu____1142 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1202 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1207,m) ->
        let uu____1213 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1213
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1214 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1216 =
      let uu____1217 = FStar_Options.ugly ()  in Prims.op_Negation uu____1217
       in
    if uu____1216
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1225 = FStar_Options.print_implicits ()  in
         if uu____1225 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1229 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1254,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1274 =
             let uu____1275 =
               let uu____1284 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1284  in
             uu____1275 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1274
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1339;_})
           ->
           let uu____1354 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1354
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1356;_})
           ->
           let uu____1371 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1371
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1389 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1417 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1435  ->
                                 match uu____1435 with
                                 | (t1,uu____1441) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1417
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1389 (FStar_String.concat "\\/")  in
           let uu____1446 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1446
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1458 = tag_of_term t  in
           let uu____1459 = sli m  in
           let uu____1460 = term_to_string t'  in
           let uu____1461 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1458 uu____1459
             uu____1460 uu____1461
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1474 = tag_of_term t  in
           let uu____1475 = term_to_string t'  in
           let uu____1476 = sli m0  in
           let uu____1477 = sli m1  in
           let uu____1478 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1474
             uu____1475 uu____1476 uu____1477 uu____1478
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1487 = FStar_Range.string_of_range r  in
           let uu____1488 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1487
             uu____1488
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1495 = lid_to_string l  in
           let uu____1496 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1497 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1495 uu____1496
             uu____1497
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1499) ->
           let uu____1504 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1504
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1506 = db_to_string x3  in
           let uu____1507 =
             let uu____1508 =
               let uu____1509 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1509 ")"  in
             Prims.strcat ":(" uu____1508  in
           Prims.strcat uu____1506 uu____1507
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar u ->
           uvar_to_string u.FStar_Syntax_Syntax.ctx_uvar_head
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1515 = FStar_Options.print_universes ()  in
           if uu____1515
           then
             let uu____1516 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1516
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1536 = binders_to_string " -> " bs  in
           let uu____1537 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1536 uu____1537
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1562 = binders_to_string " " bs  in
                let uu____1563 = term_to_string t2  in
                let uu____1564 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1568 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1568)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1562 uu____1563
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1564
            | uu____1571 ->
                let uu____1574 = binders_to_string " " bs  in
                let uu____1575 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1574 uu____1575)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1582 = bv_to_string xt  in
           let uu____1583 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1584 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1582 uu____1583 uu____1584
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1609 = term_to_string t  in
           let uu____1610 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1609 uu____1610
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1629 = lbs_to_string [] lbs  in
           let uu____1630 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1629 uu____1630
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1691 =
                   let uu____1692 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1692
                     (FStar_Util.dflt "default")
                    in
                 let uu____1697 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1691 uu____1697
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1713 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1713
              in
           let uu____1714 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1714 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1753 = term_to_string head1  in
           let uu____1754 =
             let uu____1755 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1785  ->
                       match uu____1785 with
                       | (p,wopt,e) ->
                           let uu____1801 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1802 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1804 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1804
                              in
                           let uu____1805 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1801
                             uu____1802 uu____1805))
                in
             FStar_Util.concat_l "\n\t|" uu____1755  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1753 uu____1754
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1812 = FStar_Options.print_universes ()  in
           if uu____1812
           then
             let uu____1813 = term_to_string t  in
             let uu____1814 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1813 uu____1814
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1817 =
      let uu____1818 = FStar_Options.ugly ()  in Prims.op_Negation uu____1818
       in
    if uu____1817
    then
      let e =
        let uu____1820 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1820  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1843 = fv_to_string l  in
           let uu____1844 =
             let uu____1845 =
               FStar_List.map
                 (fun uu____1856  ->
                    match uu____1856 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1845 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1843 uu____1844
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1868) ->
           let uu____1873 = FStar_Options.print_bound_var_types ()  in
           if uu____1873
           then
             let uu____1874 = bv_to_string x1  in
             let uu____1875 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1874 uu____1875
           else
             (let uu____1877 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1877)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1879 = FStar_Options.print_bound_var_types ()  in
           if uu____1879
           then
             let uu____1880 = bv_to_string x1  in
             let uu____1881 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1880 uu____1881
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1885 = FStar_Options.print_real_names ()  in
           if uu____1885
           then
             let uu____1886 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1886
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1898 = quals_to_string' quals  in
      let uu____1899 =
        let uu____1900 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1916 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1917 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1918 =
                    let uu____1919 = FStar_Options.print_universes ()  in
                    if uu____1919
                    then
                      let uu____1920 =
                        let uu____1921 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1921 ">"  in
                      Prims.strcat "<" uu____1920
                    else ""  in
                  let uu____1923 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1924 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1916
                    uu____1917 uu____1918 uu____1923 uu____1924))
           in
        FStar_Util.concat_l "\n and " uu____1900  in
      FStar_Util.format3 "%slet %s %s" uu____1898
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1899

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___73_1928  ->
    match uu___73_1928 with
    | [] -> ""
    | tms ->
        let uu____1934 =
          let uu____1935 =
            FStar_List.map
              (fun t  ->
                 let uu____1941 = term_to_string t  in paren uu____1941) tms
             in
          FStar_All.pipe_right uu____1935 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1934

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1945 = FStar_Options.print_effect_args ()  in
    if uu____1945
    then
      let uu____1946 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1946
    else
      (let uu____1948 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1949 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1948 uu____1949)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___74_1950  ->
    match uu___74_1950 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1951 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1954 = aqual_to_string aq  in Prims.strcat uu____1954 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____1961 =
        let uu____1962 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1962  in
      if uu____1961
      then
        let uu____1963 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1963 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1969 = b  in
         match uu____1969 with
         | (a,imp) ->
             let uu____1976 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1976
             then
               let uu____1977 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1977
             else
               (let uu____1979 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1981 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1981)
                   in
                if uu____1979
                then
                  let uu____1982 = nm_to_string a  in
                  imp_to_string uu____1982 imp
                else
                  (let uu____1984 =
                     let uu____1985 = nm_to_string a  in
                     let uu____1986 =
                       let uu____1987 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1987  in
                     Prims.strcat uu____1985 uu____1986  in
                   imp_to_string uu____1984 imp)))

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
        let uu____1999 = FStar_Options.print_implicits ()  in
        if uu____1999 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2003 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2003 (FStar_String.concat sep)
      else
        (let uu____2021 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2021 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___75_2030  ->
    match uu___75_2030 with
    | (a,imp) ->
        let uu____2037 = term_to_string a  in imp_to_string uu____2037 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2046 = FStar_Options.print_implicits ()  in
      if uu____2046 then args else filter_imp args  in
    let uu____2056 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2056 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2075 = FStar_Options.ugly ()  in
      if uu____2075
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2080 =
      let uu____2081 = FStar_Options.ugly ()  in Prims.op_Negation uu____2081
       in
    if uu____2080
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2095 =
             let uu____2096 = FStar_Syntax_Subst.compress t  in
             uu____2096.FStar_Syntax_Syntax.n  in
           (match uu____2095 with
            | FStar_Syntax_Syntax.Tm_type uu____2099 when
                let uu____2100 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2100 -> term_to_string t
            | uu____2101 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2103 = univ_to_string u  in
                     let uu____2104 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2103 uu____2104
                 | uu____2105 ->
                     let uu____2108 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2108))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2119 =
             let uu____2120 = FStar_Syntax_Subst.compress t  in
             uu____2120.FStar_Syntax_Syntax.n  in
           (match uu____2119 with
            | FStar_Syntax_Syntax.Tm_type uu____2123 when
                let uu____2124 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2124 -> term_to_string t
            | uu____2125 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2127 = univ_to_string u  in
                     let uu____2128 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2127 uu____2128
                 | uu____2129 ->
                     let uu____2132 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2132))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2135 = FStar_Options.print_effect_args ()  in
             if uu____2135
             then
               let uu____2136 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2137 =
                 let uu____2138 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2138 (FStar_String.concat ", ")
                  in
               let uu____2147 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2148 =
                 let uu____2149 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2149 (FStar_String.concat ", ")
                  in
               let uu____2166 =
                 let uu____2167 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2167 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2136
                 uu____2137 uu____2147 uu____2148 uu____2166
             else
               (let uu____2177 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___76_2181  ->
                           match uu___76_2181 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2182 -> false)))
                    &&
                    (let uu____2184 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2184)
                   in
                if uu____2177
                then
                  let uu____2185 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2185
                else
                  (let uu____2187 =
                     ((let uu____2190 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2190) &&
                        (let uu____2192 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2192))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2187
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2194 =
                        (let uu____2197 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2197) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___77_2201  ->
                                   match uu___77_2201 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2202 -> false)))
                         in
                      if uu____2194
                      then
                        let uu____2203 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2203
                      else
                        (let uu____2205 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2206 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2205 uu____2206))))
              in
           let dec =
             let uu____2208 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___78_2218  ->
                       match uu___78_2218 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2224 =
                             let uu____2225 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2225
                              in
                           [uu____2224]
                       | uu____2226 -> []))
                in
             FStar_All.pipe_right uu____2208 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2230 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___79_2236  ->
    match uu___79_2236 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2249 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2277 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2295  ->
                              match uu____2295 with
                              | (t,uu____2301) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2277
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2249 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2307 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2307
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2310) ->
        let uu____2311 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2311
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2319 = sli m  in
        let uu____2320 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2319 uu____2320
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2328 = sli m  in
        let uu____2329 = sli m'  in
        let uu____2330 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2328
          uu____2329 uu____2330

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2341 = FStar_Options.ugly ()  in
      if uu____2341
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
      let uu____2355 = b  in
      match uu____2355 with
      | (a,imp) ->
          let n1 =
            let uu____2359 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2359
            then FStar_Util.JsonNull
            else
              (let uu____2361 =
                 let uu____2362 = nm_to_string a  in
                 imp_to_string uu____2362 imp  in
               FStar_Util.JsonStr uu____2361)
             in
          let t =
            let uu____2364 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2364  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2387 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2387
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2399 = FStar_Options.print_universes ()  in
    if uu____2399 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2406 =
      let uu____2407 = FStar_Options.ugly ()  in Prims.op_Negation uu____2407
       in
    if uu____2406
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2411 = s  in
       match uu____2411 with
       | (us,t) ->
           let uu____2422 =
             let uu____2423 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2423  in
           let uu____2424 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2422 uu____2424)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2430 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2431 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2432 =
      let uu____2433 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2433  in
    let uu____2434 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2435 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2430 uu____2431 uu____2432
      uu____2434 uu____2435
  
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
          let uu____2460 =
            let uu____2461 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2461  in
          if uu____2460
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2475 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2475 (FStar_String.concat ",\n\t")
                in
             let uu____2484 =
               let uu____2487 =
                 let uu____2490 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2491 =
                   let uu____2494 =
                     let uu____2495 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2495  in
                   let uu____2496 =
                     let uu____2499 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2500 =
                       let uu____2503 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2504 =
                         let uu____2507 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2508 =
                           let uu____2511 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2512 =
                             let uu____2515 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2516 =
                               let uu____2519 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2520 =
                                 let uu____2523 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2524 =
                                   let uu____2527 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2528 =
                                     let uu____2531 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2532 =
                                       let uu____2535 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2536 =
                                         let uu____2539 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2540 =
                                           let uu____2543 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2544 =
                                             let uu____2547 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2548 =
                                               let uu____2551 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2552 =
                                                 let uu____2555 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2556 =
                                                   let uu____2559 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2559]  in
                                                 uu____2555 :: uu____2556  in
                                               uu____2551 :: uu____2552  in
                                             uu____2547 :: uu____2548  in
                                           uu____2543 :: uu____2544  in
                                         uu____2539 :: uu____2540  in
                                       uu____2535 :: uu____2536  in
                                     uu____2531 :: uu____2532  in
                                   uu____2527 :: uu____2528  in
                                 uu____2523 :: uu____2524  in
                               uu____2519 :: uu____2520  in
                             uu____2515 :: uu____2516  in
                           uu____2511 :: uu____2512  in
                         uu____2507 :: uu____2508  in
                       uu____2503 :: uu____2504  in
                     uu____2499 :: uu____2500  in
                   uu____2494 :: uu____2496  in
                 uu____2490 :: uu____2491  in
               (if for_free then "_for_free " else "") :: uu____2487  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2484)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2576 =
      let uu____2577 = FStar_Options.ugly ()  in Prims.op_Negation uu____2577
       in
    if uu____2576
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2583 -> ""
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
             (lid,univs1,tps,k,uu____2594,uu____2595) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2607 = FStar_Options.print_universes ()  in
             if uu____2607
             then
               let uu____2608 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2608 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2613,uu____2614,uu____2615) ->
             let uu____2620 = FStar_Options.print_universes ()  in
             if uu____2620
             then
               let uu____2621 = univ_names_to_string univs1  in
               let uu____2622 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2621
                 lid.FStar_Ident.str uu____2622
             else
               (let uu____2624 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2624)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2628 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2629 =
               let uu____2630 = FStar_Options.print_universes ()  in
               if uu____2630
               then
                 let uu____2631 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2631
               else ""  in
             let uu____2633 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2628
               lid.FStar_Ident.str uu____2629 uu____2633
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2635,f) ->
             let uu____2637 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2637
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2639) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2645 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2645
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2647) ->
             let uu____2656 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2656 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2710) -> lift_wp
               | (uu____2737,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2765 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2765 with
              | (us,t) ->
                  let uu____2772 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2773 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2774 = univ_names_to_string us  in
                  let uu____2775 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2772 uu____2773 uu____2774 uu____2775)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2785 = FStar_Options.print_universes ()  in
             if uu____2785
             then
               let uu____2786 =
                 let uu____2791 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2791  in
               (match uu____2786 with
                | (univs2,t) ->
                    let uu____2802 =
                      let uu____2807 =
                        let uu____2808 = FStar_Syntax_Subst.compress t  in
                        uu____2808.FStar_Syntax_Syntax.n  in
                      match uu____2807 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2841 -> failwith "impossible"  in
                    (match uu____2802 with
                     | (tps1,c1) ->
                         let uu____2848 = sli l  in
                         let uu____2849 = univ_names_to_string univs2  in
                         let uu____2850 = binders_to_string " " tps1  in
                         let uu____2851 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2848 uu____2849 uu____2850 uu____2851))
             else
               (let uu____2853 = sli l  in
                let uu____2854 = binders_to_string " " tps  in
                let uu____2855 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2853 uu____2854
                  uu____2855)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2862 =
               let uu____2863 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2863  in
             let uu____2868 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2862 uu____2868
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2869 ->
           let uu____2872 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2872 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2883 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2883 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2889,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2891;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2893;
                       FStar_Syntax_Syntax.lbdef = uu____2894;
                       FStar_Syntax_Syntax.lbattrs = uu____2895;
                       FStar_Syntax_Syntax.lbpos = uu____2896;_}::[]),uu____2897)
        ->
        let uu____2918 = lbname_to_string lb  in
        let uu____2919 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2918 uu____2919
    | uu____2920 ->
        let uu____2921 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2921 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2937 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2938 =
      let uu____2939 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2939 (FStar_String.concat "\n")  in
    let uu____2944 =
      let uu____2945 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2945 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2937 uu____2938 uu____2944
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___80_2954  ->
    match uu___80_2954 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2957 = FStar_Util.string_of_int i  in
        let uu____2958 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2957 uu____2958
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2961 = bv_to_string x  in
        let uu____2962 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2961 uu____2962
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2969 = bv_to_string x  in
        let uu____2970 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2969 uu____2970
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2973 = FStar_Util.string_of_int i  in
        let uu____2974 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2973 uu____2974
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2977 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2977
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2983 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2983 (FStar_String.concat "; ")
  
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
          (let uu____3021 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3021))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3028 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3028)));
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
           (let uu____3062 = f x  in
            FStar_Util.string_builder_append strb uu____3062);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3069 = f x1  in
                 FStar_Util.string_builder_append strb uu____3069)) xs;
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
           (let uu____3107 = f x  in
            FStar_Util.string_builder_append strb uu____3107);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3114 = f x1  in
                 FStar_Util.string_builder_append strb uu____3114)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3130 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3130
  
let (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____3140 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____3141 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____3142 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format3 "(%s |- %s : %s)" uu____3140 uu____3141 uu____3142
  