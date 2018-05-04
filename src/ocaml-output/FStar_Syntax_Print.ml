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
    | FStar_Syntax_Syntax.Tm_delayed (uu____1139,m) ->
        let uu____1181 = FStar_ST.op_Bang m  in
        (match uu____1181 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1241 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1246,m) ->
        let uu____1252 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1252
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1253 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1255 =
      let uu____1256 = FStar_Options.ugly ()  in Prims.op_Negation uu____1256
       in
    if uu____1255
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1264 = FStar_Options.print_implicits ()  in
         if uu____1264 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1268 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1293,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1313 =
             let uu____1314 =
               let uu____1323 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1323  in
             uu____1314 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1313
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1378;_})
           ->
           let uu____1393 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1393
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1395;_})
           ->
           let uu____1410 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1410
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1428 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1456 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1474  ->
                                 match uu____1474 with
                                 | (t1,uu____1480) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1456
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1428 (FStar_String.concat "\\/")  in
           let uu____1485 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1485
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1497 = tag_of_term t  in
           let uu____1498 = sli m  in
           let uu____1499 = term_to_string t'  in
           let uu____1500 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1497 uu____1498
             uu____1499 uu____1500
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1513 = tag_of_term t  in
           let uu____1514 = term_to_string t'  in
           let uu____1515 = sli m0  in
           let uu____1516 = sli m1  in
           let uu____1517 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1513
             uu____1514 uu____1515 uu____1516 uu____1517
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1526 = FStar_Range.string_of_range r  in
           let uu____1527 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1526
             uu____1527
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1534 = lid_to_string l  in
           let uu____1535 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1536 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1534 uu____1535
             uu____1536
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1538) ->
           let uu____1543 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1543
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1545 = db_to_string x3  in
           let uu____1546 =
             let uu____1547 =
               let uu____1548 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1548 ")"  in
             Prims.strcat ":(" uu____1547  in
           Prims.strcat uu____1545 uu____1546
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,[]) -> ctx_uvar_to_string u
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1560 = ctx_uvar_to_string u  in
           let uu____1561 = subst_to_string s  in
           FStar_Util.format2 "(%s @ %s)" uu____1560 uu____1561
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1564 = FStar_Options.print_universes ()  in
           if uu____1564
           then
             let uu____1565 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1565
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1585 = binders_to_string " -> " bs  in
           let uu____1586 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1585 uu____1586
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1611 = binders_to_string " " bs  in
                let uu____1612 = term_to_string t2  in
                let uu____1613 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1617 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1617)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1611 uu____1612
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1613
            | uu____1620 ->
                let uu____1623 = binders_to_string " " bs  in
                let uu____1624 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1623 uu____1624)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1631 = bv_to_string xt  in
           let uu____1632 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1633 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1631 uu____1632 uu____1633
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1658 = term_to_string t  in
           let uu____1659 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1658 uu____1659
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1678 = lbs_to_string [] lbs  in
           let uu____1679 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1678 uu____1679
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1740 =
                   let uu____1741 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1741
                     (FStar_Util.dflt "default")
                    in
                 let uu____1746 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1740 uu____1746
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1762 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1762
              in
           let uu____1763 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1763 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1802 = term_to_string head1  in
           let uu____1803 =
             let uu____1804 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1834  ->
                       match uu____1834 with
                       | (p,wopt,e) ->
                           let uu____1850 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1851 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1853 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1853
                              in
                           let uu____1854 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1850
                             uu____1851 uu____1854))
                in
             FStar_Util.concat_l "\n\t|" uu____1804  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1802 uu____1803
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1861 = FStar_Options.print_universes ()  in
           if uu____1861
           then
             let uu____1862 = term_to_string t  in
             let uu____1863 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1862 uu____1863
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1866 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1867 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1868 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1866 uu____1867
      uu____1868

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___99_1869  ->
    match uu___99_1869 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1872 = FStar_Util.string_of_int i  in
        let uu____1873 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1872 uu____1873
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1876 = bv_to_string x  in
        let uu____1877 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1876 uu____1877
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1884 = bv_to_string x  in
        let uu____1885 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____1884 uu____1885
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1888 = FStar_Util.string_of_int i  in
        let uu____1889 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1888 uu____1889
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1892 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1892

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1894 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1894 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1904 =
      let uu____1905 = FStar_Options.ugly ()  in Prims.op_Negation uu____1905
       in
    if uu____1904
    then
      let e =
        let uu____1907 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1907  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1930 = fv_to_string l  in
           let uu____1931 =
             let uu____1932 =
               FStar_List.map
                 (fun uu____1943  ->
                    match uu____1943 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1932 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1930 uu____1931
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1955) ->
           let uu____1960 = FStar_Options.print_bound_var_types ()  in
           if uu____1960
           then
             let uu____1961 = bv_to_string x1  in
             let uu____1962 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1961 uu____1962
           else
             (let uu____1964 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1964)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1966 = FStar_Options.print_bound_var_types ()  in
           if uu____1966
           then
             let uu____1967 = bv_to_string x1  in
             let uu____1968 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1967 uu____1968
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1972 = FStar_Options.print_real_names ()  in
           if uu____1972
           then
             let uu____1973 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1973
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1985 = quals_to_string' quals  in
      let uu____1986 =
        let uu____1987 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2003 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2004 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2005 =
                    let uu____2006 = FStar_Options.print_universes ()  in
                    if uu____2006
                    then
                      let uu____2007 =
                        let uu____2008 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2008 ">"  in
                      Prims.strcat "<" uu____2007
                    else ""  in
                  let uu____2010 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2011 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2003
                    uu____2004 uu____2005 uu____2010 uu____2011))
           in
        FStar_Util.concat_l "\n and " uu____1987  in
      FStar_Util.format3 "%slet %s %s" uu____1985
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1986

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___100_2015  ->
    match uu___100_2015 with
    | [] -> ""
    | tms ->
        let uu____2021 =
          let uu____2022 =
            FStar_List.map
              (fun t  ->
                 let uu____2028 = term_to_string t  in paren uu____2028) tms
             in
          FStar_All.pipe_right uu____2022 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2021

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2032 = FStar_Options.print_effect_args ()  in
    if uu____2032
    then
      let uu____2033 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2033
    else
      (let uu____2035 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2036 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2035 uu____2036)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___101_2037  ->
    match uu___101_2037 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2038 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2041 = aqual_to_string aq  in Prims.strcat uu____2041 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2048 =
        let uu____2049 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2049  in
      if uu____2048
      then
        let uu____2050 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2050 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2056 = b  in
         match uu____2056 with
         | (a,imp) ->
             let uu____2063 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2063
             then
               let uu____2064 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2064
             else
               (let uu____2066 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2068 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2068)
                   in
                if uu____2066
                then
                  let uu____2069 = nm_to_string a  in
                  imp_to_string uu____2069 imp
                else
                  (let uu____2071 =
                     let uu____2072 = nm_to_string a  in
                     let uu____2073 =
                       let uu____2074 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2074  in
                     Prims.strcat uu____2072 uu____2073  in
                   imp_to_string uu____2071 imp)))

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
        let uu____2090 = FStar_Options.print_implicits ()  in
        if uu____2090 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2098 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2098 (FStar_String.concat sep)
      else
        (let uu____2116 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2116 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___102_2125  ->
    match uu___102_2125 with
    | (a,imp) ->
        let uu____2132 = term_to_string a  in imp_to_string uu____2132 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2141 = FStar_Options.print_implicits ()  in
      if uu____2141 then args else filter_imp args  in
    let uu____2151 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2151 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2170 = FStar_Options.ugly ()  in
      if uu____2170
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2175 =
      let uu____2176 = FStar_Options.ugly ()  in Prims.op_Negation uu____2176
       in
    if uu____2175
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2190 =
             let uu____2191 = FStar_Syntax_Subst.compress t  in
             uu____2191.FStar_Syntax_Syntax.n  in
           (match uu____2190 with
            | FStar_Syntax_Syntax.Tm_type uu____2194 when
                let uu____2195 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2195 -> term_to_string t
            | uu____2196 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2198 = univ_to_string u  in
                     let uu____2199 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2198 uu____2199
                 | uu____2200 ->
                     let uu____2203 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2203))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2214 =
             let uu____2215 = FStar_Syntax_Subst.compress t  in
             uu____2215.FStar_Syntax_Syntax.n  in
           (match uu____2214 with
            | FStar_Syntax_Syntax.Tm_type uu____2218 when
                let uu____2219 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2219 -> term_to_string t
            | uu____2220 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2222 = univ_to_string u  in
                     let uu____2223 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2222 uu____2223
                 | uu____2224 ->
                     let uu____2227 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2227))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2230 = FStar_Options.print_effect_args ()  in
             if uu____2230
             then
               let uu____2231 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2232 =
                 let uu____2233 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2233 (FStar_String.concat ", ")
                  in
               let uu____2242 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2243 =
                 let uu____2244 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2244 (FStar_String.concat ", ")
                  in
               let uu____2261 =
                 let uu____2262 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2262 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2231
                 uu____2232 uu____2242 uu____2243 uu____2261
             else
               (let uu____2272 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___103_2276  ->
                           match uu___103_2276 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2277 -> false)))
                    &&
                    (let uu____2279 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2279)
                   in
                if uu____2272
                then
                  let uu____2280 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2280
                else
                  (let uu____2282 =
                     ((let uu____2285 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2285) &&
                        (let uu____2287 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2287))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2282
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2289 =
                        (let uu____2292 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2292) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___104_2296  ->
                                   match uu___104_2296 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2297 -> false)))
                         in
                      if uu____2289
                      then
                        let uu____2298 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2298
                      else
                        (let uu____2300 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2301 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2300 uu____2301))))
              in
           let dec =
             let uu____2303 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___105_2313  ->
                       match uu___105_2313 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2319 =
                             let uu____2320 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2320
                              in
                           [uu____2319]
                       | uu____2321 -> []))
                in
             FStar_All.pipe_right uu____2303 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2325 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___106_2331  ->
    match uu___106_2331 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2344 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2372 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2390  ->
                              match uu____2390 with
                              | (t,uu____2396) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2372
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2344 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2402 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2402
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2405) ->
        let uu____2406 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2406
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2414 = sli m  in
        let uu____2415 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2414 uu____2415
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2423 = sli m  in
        let uu____2424 = sli m'  in
        let uu____2425 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2423
          uu____2424 uu____2425

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2436 = FStar_Options.ugly ()  in
      if uu____2436
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
      let uu____2450 = b  in
      match uu____2450 with
      | (a,imp) ->
          let n1 =
            let uu____2454 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2454
            then FStar_Util.JsonNull
            else
              (let uu____2456 =
                 let uu____2457 = nm_to_string a  in
                 imp_to_string uu____2457 imp  in
               FStar_Util.JsonStr uu____2456)
             in
          let t =
            let uu____2459 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2459  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2482 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2482
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2494 = FStar_Options.print_universes ()  in
    if uu____2494 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2501 =
      let uu____2502 = FStar_Options.ugly ()  in Prims.op_Negation uu____2502
       in
    if uu____2501
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2506 = s  in
       match uu____2506 with
       | (us,t) ->
           let uu____2517 =
             let uu____2518 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2518  in
           let uu____2519 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2517 uu____2519)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2525 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2526 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2527 =
      let uu____2528 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2528  in
    let uu____2529 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2530 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2525 uu____2526 uu____2527
      uu____2529 uu____2530
  
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
          let uu____2555 =
            let uu____2556 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2556  in
          if uu____2555
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2570 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2570 (FStar_String.concat ",\n\t")
                in
             let uu____2579 =
               let uu____2582 =
                 let uu____2585 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2586 =
                   let uu____2589 =
                     let uu____2590 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2590  in
                   let uu____2591 =
                     let uu____2594 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2595 =
                       let uu____2598 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2599 =
                         let uu____2602 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2603 =
                           let uu____2606 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2607 =
                             let uu____2610 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2611 =
                               let uu____2614 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2615 =
                                 let uu____2618 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2619 =
                                   let uu____2622 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2623 =
                                     let uu____2626 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2627 =
                                       let uu____2630 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2631 =
                                         let uu____2634 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2635 =
                                           let uu____2638 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2639 =
                                             let uu____2642 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2643 =
                                               let uu____2646 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2647 =
                                                 let uu____2650 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2651 =
                                                   let uu____2654 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2654]  in
                                                 uu____2650 :: uu____2651  in
                                               uu____2646 :: uu____2647  in
                                             uu____2642 :: uu____2643  in
                                           uu____2638 :: uu____2639  in
                                         uu____2634 :: uu____2635  in
                                       uu____2630 :: uu____2631  in
                                     uu____2626 :: uu____2627  in
                                   uu____2622 :: uu____2623  in
                                 uu____2618 :: uu____2619  in
                               uu____2614 :: uu____2615  in
                             uu____2610 :: uu____2611  in
                           uu____2606 :: uu____2607  in
                         uu____2602 :: uu____2603  in
                       uu____2598 :: uu____2599  in
                     uu____2594 :: uu____2595  in
                   uu____2589 :: uu____2591  in
                 uu____2585 :: uu____2586  in
               (if for_free then "_for_free " else "") :: uu____2582  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2579)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2671 =
      let uu____2672 = FStar_Options.ugly ()  in Prims.op_Negation uu____2672
       in
    if uu____2671
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2678 -> ""
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
             (lid,univs1,tps,k,uu____2689,uu____2690) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2702 = FStar_Options.print_universes ()  in
             if uu____2702
             then
               let uu____2703 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2703 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2708,uu____2709,uu____2710) ->
             let uu____2715 = FStar_Options.print_universes ()  in
             if uu____2715
             then
               let uu____2716 = univ_names_to_string univs1  in
               let uu____2717 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2716
                 lid.FStar_Ident.str uu____2717
             else
               (let uu____2719 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2719)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2723 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2724 =
               let uu____2725 = FStar_Options.print_universes ()  in
               if uu____2725
               then
                 let uu____2726 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2726
               else ""  in
             let uu____2728 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2723
               lid.FStar_Ident.str uu____2724 uu____2728
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2730,f) ->
             let uu____2732 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2732
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2734) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2740 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2740
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2742) ->
             let uu____2751 =
               let uu____2752 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2752 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2751
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2782) -> lift_wp
               | (uu____2789,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2797 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2797 with
              | (us,t) ->
                  let uu____2804 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2805 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2806 = univ_names_to_string us  in
                  let uu____2807 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2804 uu____2805 uu____2806 uu____2807)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2817 = FStar_Options.print_universes ()  in
             if uu____2817
             then
               let uu____2818 =
                 let uu____2823 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2823  in
               (match uu____2818 with
                | (univs2,t) ->
                    let uu____2834 =
                      let uu____2847 =
                        let uu____2848 = FStar_Syntax_Subst.compress t  in
                        uu____2848.FStar_Syntax_Syntax.n  in
                      match uu____2847 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2889 -> failwith "impossible"  in
                    (match uu____2834 with
                     | (tps1,c1) ->
                         let uu____2920 = sli l  in
                         let uu____2921 = univ_names_to_string univs2  in
                         let uu____2922 = binders_to_string " " tps1  in
                         let uu____2923 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2920 uu____2921 uu____2922 uu____2923))
             else
               (let uu____2925 = sli l  in
                let uu____2926 = binders_to_string " " tps  in
                let uu____2927 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2925 uu____2926
                  uu____2927)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2934 =
               let uu____2935 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2935  in
             let uu____2940 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2934 uu____2940
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2941 ->
           let uu____2944 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2944 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2955 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2955 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2961,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2963;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2965;
                       FStar_Syntax_Syntax.lbdef = uu____2966;
                       FStar_Syntax_Syntax.lbattrs = uu____2967;
                       FStar_Syntax_Syntax.lbpos = uu____2968;_}::[]),uu____2969)
        ->
        let uu____2990 = lbname_to_string lb  in
        let uu____2991 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2990 uu____2991
    | uu____2992 ->
        let uu____2993 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2993 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3009 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3010 =
      let uu____3011 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3011 (FStar_String.concat "\n")  in
    let uu____3016 =
      let uu____3017 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3017 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3009 uu____3010 uu____3016
  
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
          (let uu____3051 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3051))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3058 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3058)));
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
           (let uu____3092 = f x  in
            FStar_Util.string_builder_append strb uu____3092);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3099 = f x1  in
                 FStar_Util.string_builder_append strb uu____3099)) xs;
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
           (let uu____3137 = f x  in
            FStar_Util.string_builder_append strb uu____3137);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3144 = f x1  in
                 FStar_Util.string_builder_append strb uu____3144)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3160 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3160
  