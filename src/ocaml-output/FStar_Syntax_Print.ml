open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___94_5  ->
    match uu___94_5 with
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
  'Auu____271 'Auu____272 .
    ('Auu____271,'Auu____272) FStar_Util.either -> Prims.bool
  =
  fun uu___95_281  ->
    match uu___95_281 with
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
         (fun uu___96_347  ->
            match uu___96_347 with
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
          let uu____438 =
            let uu____443 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____443  in
          (match uu____438 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____453 =
                 let uu____456 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____456 :: xs  in
               FStar_Pervasives_Native.Some uu____453
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____466 ->
        let uu____467 = is_lex_top e  in
        if uu____467
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____508 = f hd1  in if uu____508 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____532 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____532
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____556 = get_lid e  in find_lid uu____556 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____566 = get_lid e  in find_lid uu____566 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____576 = get_lid t  in find_lid uu____576 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___97_586  ->
    match uu___97_586 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____594 = FStar_Options.hide_uvar_nums ()  in
    if uu____594
    then "?"
    else
      (let uu____596 =
         let uu____597 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____597 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____596)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____603 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____604 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____603 uu____604
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
     FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun u  ->
    let uu____626 = FStar_Options.hide_uvar_nums ()  in
    if uu____626
    then "?"
    else
      (let uu____628 =
         let uu____629 =
           let uu____630 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____630 FStar_Util.string_of_int  in
         let uu____631 =
           let uu____632 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____632  in
         Prims.strcat uu____629 uu____631  in
       Prims.strcat "?" uu____628)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____653 = FStar_Syntax_Subst.compress_univ u  in
      match uu____653 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____663 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____671 =
      let uu____672 = FStar_Options.ugly ()  in Prims.op_Negation uu____672
       in
    if uu____671
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____676 = FStar_Syntax_Subst.compress_univ u  in
       match uu____676 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____688 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____688
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____690 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____690 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____704 = univ_to_string u2  in
                let uu____705 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____704 uu____705)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____709 =
             let uu____710 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____710 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____709
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____724 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____724 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____734 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____734 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___98_745  ->
    match uu___98_745 with
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
        let uu____747 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____747
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____750 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____750 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____761 =
          let uu____762 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____762  in
        let uu____763 =
          let uu____764 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____764 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____761 uu____763
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____783 =
          let uu____784 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____784  in
        let uu____785 =
          let uu____786 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____786 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____783 uu____785
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____796 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____796
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
    | uu____807 ->
        let uu____810 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____810 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____828 ->
        let uu____831 = quals_to_string quals  in Prims.strcat uu____831 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____971 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____971
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____973 = nm_to_string x  in Prims.strcat "Tm_name: " uu____973
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____975 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____975
    | FStar_Syntax_Syntax.Tm_uinst uu____976 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____983 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____984 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____985,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____986;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1001,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1002;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1017 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1034 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1047 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1054 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1069 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1092 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1119 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1132 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1147,m) ->
        let uu____1189 = FStar_ST.op_Bang m  in
        (match uu____1189 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1249 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1254,m) ->
        let uu____1260 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1260
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1261 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1263 =
      let uu____1264 = FStar_Options.ugly ()  in Prims.op_Negation uu____1264
       in
    if uu____1263
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1272 = FStar_Options.print_implicits ()  in
         if uu____1272 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1276 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1301,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1321 =
             let uu____1322 =
               let uu____1331 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1331  in
             uu____1322 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1321
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1386;_})
           ->
           let uu____1401 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1401
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1403;_})
           ->
           let uu____1418 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1418
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1436 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1464 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1482  ->
                                 match uu____1482 with
                                 | (t1,uu____1488) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1464
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1436 (FStar_String.concat "\\/")  in
           let uu____1493 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1493
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1505 = tag_of_term t  in
           let uu____1506 = sli m  in
           let uu____1507 = term_to_string t'  in
           let uu____1508 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1505 uu____1506
             uu____1507 uu____1508
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1521 = tag_of_term t  in
           let uu____1522 = term_to_string t'  in
           let uu____1523 = sli m0  in
           let uu____1524 = sli m1  in
           let uu____1525 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1521
             uu____1522 uu____1523 uu____1524 uu____1525
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1534 = FStar_Range.string_of_range r  in
           let uu____1535 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1534
             uu____1535
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1542 = lid_to_string l  in
           let uu____1543 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1544 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1542 uu____1543
             uu____1544
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1546) ->
           let uu____1551 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1551
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1553 = db_to_string x3  in
           let uu____1554 =
             let uu____1555 =
               let uu____1556 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1556 ")"  in
             Prims.strcat ":(" uu____1555  in
           Prims.strcat uu____1553 uu____1554
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1560)) ->
           ctx_uvar_to_string u
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1603 = ctx_uvar_to_string u  in
           let uu____1604 =
             let uu____1605 =
               FStar_List.map subst_to_string (FStar_Pervasives_Native.fst s)
                in
             FStar_All.pipe_right uu____1605 (FStar_String.concat "; ")  in
           FStar_Util.format2 "(%s @ %s)" uu____1603 uu____1604
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1620 = FStar_Options.print_universes ()  in
           if uu____1620
           then
             let uu____1621 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1621
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1641 = binders_to_string " -> " bs  in
           let uu____1642 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1641 uu____1642
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1667 = binders_to_string " " bs  in
                let uu____1668 = term_to_string t2  in
                let uu____1669 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1673 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1673)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1667 uu____1668
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1669
            | uu____1676 ->
                let uu____1679 = binders_to_string " " bs  in
                let uu____1680 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1679 uu____1680)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1687 = bv_to_string xt  in
           let uu____1688 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1689 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1687 uu____1688 uu____1689
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1714 = term_to_string t  in
           let uu____1715 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1714 uu____1715
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1734 = lbs_to_string [] lbs  in
           let uu____1735 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1734 uu____1735
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1796 =
                   let uu____1797 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1797
                     (FStar_Util.dflt "default")
                    in
                 let uu____1802 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1796 uu____1802
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1818 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1818
              in
           let uu____1819 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1819 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1858 = term_to_string head1  in
           let uu____1859 =
             let uu____1860 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1890  ->
                       match uu____1890 with
                       | (p,wopt,e) ->
                           let uu____1906 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1907 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1909 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1909
                              in
                           let uu____1910 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1906
                             uu____1907 uu____1910))
                in
             FStar_Util.concat_l "\n\t|" uu____1860  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1858 uu____1859
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1917 = FStar_Options.print_universes ()  in
           if uu____1917
           then
             let uu____1918 = term_to_string t  in
             let uu____1919 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1918 uu____1919
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1922 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1923 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1924 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1922 uu____1923
      uu____1924

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___99_1925  ->
    match uu___99_1925 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1928 = FStar_Util.string_of_int i  in
        let uu____1929 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1928 uu____1929
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1932 = bv_to_string x  in
        let uu____1933 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1932 uu____1933
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1940 = bv_to_string x  in
        let uu____1941 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____1940 uu____1941
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1944 = FStar_Util.string_of_int i  in
        let uu____1945 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1944 uu____1945
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1948 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1948

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1950 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1950 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1960 =
      let uu____1961 = FStar_Options.ugly ()  in Prims.op_Negation uu____1961
       in
    if uu____1960
    then
      let e =
        let uu____1963 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1963  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1986 = fv_to_string l  in
           let uu____1987 =
             let uu____1988 =
               FStar_List.map
                 (fun uu____1999  ->
                    match uu____1999 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1988 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1986 uu____1987
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2011) ->
           let uu____2016 = FStar_Options.print_bound_var_types ()  in
           if uu____2016
           then
             let uu____2017 = bv_to_string x1  in
             let uu____2018 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2017 uu____2018
           else
             (let uu____2020 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2020)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2022 = FStar_Options.print_bound_var_types ()  in
           if uu____2022
           then
             let uu____2023 = bv_to_string x1  in
             let uu____2024 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2023 uu____2024
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2028 = FStar_Options.print_real_names ()  in
           if uu____2028
           then
             let uu____2029 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2029
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2041 = quals_to_string' quals  in
      let uu____2042 =
        let uu____2043 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2059 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2060 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2061 =
                    let uu____2062 = FStar_Options.print_universes ()  in
                    if uu____2062
                    then
                      let uu____2063 =
                        let uu____2064 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2064 ">"  in
                      Prims.strcat "<" uu____2063
                    else ""  in
                  let uu____2066 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2067 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2059
                    uu____2060 uu____2061 uu____2066 uu____2067))
           in
        FStar_Util.concat_l "\n and " uu____2043  in
      FStar_Util.format3 "%slet %s %s" uu____2041
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2042

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___100_2071  ->
    match uu___100_2071 with
    | [] -> ""
    | tms ->
        let uu____2077 =
          let uu____2078 =
            FStar_List.map
              (fun t  ->
                 let uu____2084 = term_to_string t  in paren uu____2084) tms
             in
          FStar_All.pipe_right uu____2078 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2077

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2088 = FStar_Options.print_effect_args ()  in
    if uu____2088
    then
      let uu____2089 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2089
    else
      (let uu____2091 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2092 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2091 uu____2092)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___101_2093  ->
    match uu___101_2093 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2094 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2097 = aqual_to_string aq  in Prims.strcat uu____2097 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2104 =
        let uu____2105 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2105  in
      if uu____2104
      then
        let uu____2106 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2106 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2112 = b  in
         match uu____2112 with
         | (a,imp) ->
             let uu____2119 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2119
             then
               let uu____2120 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2120
             else
               (let uu____2122 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2124 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2124)
                   in
                if uu____2122
                then
                  let uu____2125 = nm_to_string a  in
                  imp_to_string uu____2125 imp
                else
                  (let uu____2127 =
                     let uu____2128 = nm_to_string a  in
                     let uu____2129 =
                       let uu____2130 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2130  in
                     Prims.strcat uu____2128 uu____2129  in
                   imp_to_string uu____2127 imp)))

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
        let uu____2146 = FStar_Options.print_implicits ()  in
        if uu____2146 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2154 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2154 (FStar_String.concat sep)
      else
        (let uu____2172 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2172 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___102_2181  ->
    match uu___102_2181 with
    | (a,imp) ->
        let uu____2188 = term_to_string a  in imp_to_string uu____2188 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2197 = FStar_Options.print_implicits ()  in
      if uu____2197 then args else filter_imp args  in
    let uu____2207 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2207 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2226 = FStar_Options.ugly ()  in
      if uu____2226
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2231 =
      let uu____2232 = FStar_Options.ugly ()  in Prims.op_Negation uu____2232
       in
    if uu____2231
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2246 =
             let uu____2247 = FStar_Syntax_Subst.compress t  in
             uu____2247.FStar_Syntax_Syntax.n  in
           (match uu____2246 with
            | FStar_Syntax_Syntax.Tm_type uu____2250 when
                let uu____2251 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2251 -> term_to_string t
            | uu____2252 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2254 = univ_to_string u  in
                     let uu____2255 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2254 uu____2255
                 | uu____2256 ->
                     let uu____2259 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2259))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2270 =
             let uu____2271 = FStar_Syntax_Subst.compress t  in
             uu____2271.FStar_Syntax_Syntax.n  in
           (match uu____2270 with
            | FStar_Syntax_Syntax.Tm_type uu____2274 when
                let uu____2275 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2275 -> term_to_string t
            | uu____2276 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2278 = univ_to_string u  in
                     let uu____2279 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2278 uu____2279
                 | uu____2280 ->
                     let uu____2283 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2283))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2286 = FStar_Options.print_effect_args ()  in
             if uu____2286
             then
               let uu____2287 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2288 =
                 let uu____2289 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2289 (FStar_String.concat ", ")
                  in
               let uu____2298 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2299 =
                 let uu____2300 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2300 (FStar_String.concat ", ")
                  in
               let uu____2317 =
                 let uu____2318 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2318 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2287
                 uu____2288 uu____2298 uu____2299 uu____2317
             else
               (let uu____2328 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___103_2332  ->
                           match uu___103_2332 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2333 -> false)))
                    &&
                    (let uu____2335 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2335)
                   in
                if uu____2328
                then
                  let uu____2336 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2336
                else
                  (let uu____2338 =
                     ((let uu____2341 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2341) &&
                        (let uu____2343 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2343))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2338
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2345 =
                        (let uu____2348 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2348) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___104_2352  ->
                                   match uu___104_2352 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2353 -> false)))
                         in
                      if uu____2345
                      then
                        let uu____2354 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2354
                      else
                        (let uu____2356 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2357 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2356 uu____2357))))
              in
           let dec =
             let uu____2359 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___105_2369  ->
                       match uu___105_2369 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2375 =
                             let uu____2376 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2376
                              in
                           [uu____2375]
                       | uu____2377 -> []))
                in
             FStar_All.pipe_right uu____2359 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2381 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___106_2387  ->
    match uu___106_2387 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2400 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2428 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2446  ->
                              match uu____2446 with
                              | (t,uu____2452) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2428
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2400 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2458 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2458
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2461) ->
        let uu____2462 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2462
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2470 = sli m  in
        let uu____2471 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2470 uu____2471
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2479 = sli m  in
        let uu____2480 = sli m'  in
        let uu____2481 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2479
          uu____2480 uu____2481

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2492 = FStar_Options.ugly ()  in
      if uu____2492
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
      let uu____2506 = b  in
      match uu____2506 with
      | (a,imp) ->
          let n1 =
            let uu____2510 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2510
            then FStar_Util.JsonNull
            else
              (let uu____2512 =
                 let uu____2513 = nm_to_string a  in
                 imp_to_string uu____2513 imp  in
               FStar_Util.JsonStr uu____2512)
             in
          let t =
            let uu____2515 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2515  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2538 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2538
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2550 = FStar_Options.print_universes ()  in
    if uu____2550 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2557 =
      let uu____2558 = FStar_Options.ugly ()  in Prims.op_Negation uu____2558
       in
    if uu____2557
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2562 = s  in
       match uu____2562 with
       | (us,t) ->
           let uu____2573 =
             let uu____2574 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2574  in
           let uu____2575 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2573 uu____2575)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2581 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2582 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2583 =
      let uu____2584 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2584  in
    let uu____2585 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2586 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2581 uu____2582 uu____2583
      uu____2585 uu____2586
  
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
          let uu____2611 =
            let uu____2612 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2612  in
          if uu____2611
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2626 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2626 (FStar_String.concat ",\n\t")
                in
             let uu____2635 =
               let uu____2638 =
                 let uu____2641 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2642 =
                   let uu____2645 =
                     let uu____2646 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2646  in
                   let uu____2647 =
                     let uu____2650 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2651 =
                       let uu____2654 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2655 =
                         let uu____2658 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2659 =
                           let uu____2662 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2663 =
                             let uu____2666 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2667 =
                               let uu____2670 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2671 =
                                 let uu____2674 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2675 =
                                   let uu____2678 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2679 =
                                     let uu____2682 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2683 =
                                       let uu____2686 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2687 =
                                         let uu____2690 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2691 =
                                           let uu____2694 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2695 =
                                             let uu____2698 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2699 =
                                               let uu____2702 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2703 =
                                                 let uu____2706 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2707 =
                                                   let uu____2710 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2710]  in
                                                 uu____2706 :: uu____2707  in
                                               uu____2702 :: uu____2703  in
                                             uu____2698 :: uu____2699  in
                                           uu____2694 :: uu____2695  in
                                         uu____2690 :: uu____2691  in
                                       uu____2686 :: uu____2687  in
                                     uu____2682 :: uu____2683  in
                                   uu____2678 :: uu____2679  in
                                 uu____2674 :: uu____2675  in
                               uu____2670 :: uu____2671  in
                             uu____2666 :: uu____2667  in
                           uu____2662 :: uu____2663  in
                         uu____2658 :: uu____2659  in
                       uu____2654 :: uu____2655  in
                     uu____2650 :: uu____2651  in
                   uu____2645 :: uu____2647  in
                 uu____2641 :: uu____2642  in
               (if for_free then "_for_free " else "") :: uu____2638  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2635)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2727 =
      let uu____2728 = FStar_Options.ugly ()  in Prims.op_Negation uu____2728
       in
    if uu____2727
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2734 -> ""
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
             (lid,univs1,tps,k,uu____2745,uu____2746) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2758 = FStar_Options.print_universes ()  in
             if uu____2758
             then
               let uu____2759 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2759 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2764,uu____2765,uu____2766) ->
             let uu____2771 = FStar_Options.print_universes ()  in
             if uu____2771
             then
               let uu____2772 = univ_names_to_string univs1  in
               let uu____2773 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2772
                 lid.FStar_Ident.str uu____2773
             else
               (let uu____2775 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2775)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2779 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2780 =
               let uu____2781 = FStar_Options.print_universes ()  in
               if uu____2781
               then
                 let uu____2782 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2782
               else ""  in
             let uu____2784 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2779
               lid.FStar_Ident.str uu____2780 uu____2784
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2786,f) ->
             let uu____2788 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2788
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2790) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2796 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2796
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2798) ->
             let uu____2807 =
               let uu____2808 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2808 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2807
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2838) -> lift_wp
               | (uu____2845,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2853 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2853 with
              | (us,t) ->
                  let uu____2860 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2861 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2862 = univ_names_to_string us  in
                  let uu____2863 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2860 uu____2861 uu____2862 uu____2863)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2873 = FStar_Options.print_universes ()  in
             if uu____2873
             then
               let uu____2874 =
                 let uu____2879 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2879  in
               (match uu____2874 with
                | (univs2,t) ->
                    let uu____2890 =
                      let uu____2903 =
                        let uu____2904 = FStar_Syntax_Subst.compress t  in
                        uu____2904.FStar_Syntax_Syntax.n  in
                      match uu____2903 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2945 -> failwith "impossible"  in
                    (match uu____2890 with
                     | (tps1,c1) ->
                         let uu____2976 = sli l  in
                         let uu____2977 = univ_names_to_string univs2  in
                         let uu____2978 = binders_to_string " " tps1  in
                         let uu____2979 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2976 uu____2977 uu____2978 uu____2979))
             else
               (let uu____2981 = sli l  in
                let uu____2982 = binders_to_string " " tps  in
                let uu____2983 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2981 uu____2982
                  uu____2983)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2990 =
               let uu____2991 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2991  in
             let uu____2996 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2990 uu____2996
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2997 ->
           let uu____3000 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____3000 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3011 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3011 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3017,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3019;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3021;
                       FStar_Syntax_Syntax.lbdef = uu____3022;
                       FStar_Syntax_Syntax.lbattrs = uu____3023;
                       FStar_Syntax_Syntax.lbpos = uu____3024;_}::[]),uu____3025)
        ->
        let uu____3046 = lbname_to_string lb  in
        let uu____3047 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3046 uu____3047
    | uu____3048 ->
        let uu____3049 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3049 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3065 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3066 =
      let uu____3067 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3067 (FStar_String.concat "\n")  in
    let uu____3072 =
      let uu____3073 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3073 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3065 uu____3066 uu____3072
  
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
          (let uu____3107 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3107))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3114 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3114)));
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
           (let uu____3148 = f x  in
            FStar_Util.string_builder_append strb uu____3148);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3155 = f x1  in
                 FStar_Util.string_builder_append strb uu____3155)) xs;
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
           (let uu____3193 = f x  in
            FStar_Util.string_builder_append strb uu____3193);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3200 = f x1  in
                 FStar_Util.string_builder_append strb uu____3200)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3216 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3216
  