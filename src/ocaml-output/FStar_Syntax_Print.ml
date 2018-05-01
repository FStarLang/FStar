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
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____376 =
      let uu____377 = FStar_Syntax_Subst.compress e  in
      uu____377.FStar_Syntax_Syntax.n  in
    match uu____376 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____440 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____440
        then
          let uu____449 =
            let uu____456 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____456  in
          (match uu____449 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____474 =
                 let uu____479 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____479 :: xs  in
               FStar_Pervasives_Native.Some uu____474
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____503 ->
        let uu____504 = is_lex_top e  in
        if uu____504
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____553 = f hd1  in if uu____553 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____577 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____577
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____601 = get_lid e  in find_lid uu____601 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____611 = get_lid e  in find_lid uu____611 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____621 = get_lid t  in find_lid uu____621 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___97_631  ->
    match uu___97_631 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____639 = FStar_Options.hide_uvar_nums ()  in
    if uu____639
    then "?"
    else
      (let uu____641 =
         let uu____642 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____642 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____641)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____648 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____649 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____648 uu____649
  
let (univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string)
  =
  fun u  ->
    let uu____655 = FStar_Options.hide_uvar_nums ()  in
    if uu____655
    then "?"
    else
      (let uu____657 =
         let uu____658 =
           let uu____659 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____659 FStar_Util.string_of_int  in
         let uu____660 =
           let uu____661 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____661  in
         Prims.strcat uu____658 uu____660  in
       Prims.strcat "?" uu____657)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____682 = FStar_Syntax_Subst.compress_univ u  in
      match uu____682 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____692 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____700 =
      let uu____701 = FStar_Options.ugly ()  in Prims.op_Negation uu____701
       in
    if uu____700
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____705 = FStar_Syntax_Subst.compress_univ u  in
       match uu____705 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____717 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____717
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____719 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____719 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____733 = univ_to_string u2  in
                let uu____734 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____733 uu____734)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____738 =
             let uu____739 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____739 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____738
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____753 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____753 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____763 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____763 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___98_774  ->
    match uu___98_774 with
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
        let uu____776 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____776
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____779 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____779 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____790 =
          let uu____791 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____791  in
        let uu____792 =
          let uu____793 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____793 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____790 uu____792
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____812 =
          let uu____813 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____813  in
        let uu____814 =
          let uu____815 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____815 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____812 uu____814
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____825 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____825
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
    | uu____836 ->
        let uu____839 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____839 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____857 ->
        let uu____860 = quals_to_string quals  in Prims.strcat uu____860 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____980 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____980
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____982 = nm_to_string x  in Prims.strcat "Tm_name: " uu____982
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____984 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____984
    | FStar_Syntax_Syntax.Tm_uinst uu____985 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____992 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____993 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____994,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____995;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1010,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1011;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1026 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1043 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1056 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1063 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1078 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1101 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1128 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1141 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1158,m) ->
        let uu____1200 = FStar_ST.op_Bang m  in
        (match uu____1200 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1260 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1265,m) ->
        let uu____1271 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1271
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1272 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1274 =
      let uu____1275 = FStar_Options.ugly ()  in Prims.op_Negation uu____1275
       in
    if uu____1274
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1281 = FStar_Options.print_implicits ()  in
         if uu____1281 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1283 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1308,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1328 =
             let uu____1329 =
               let uu____1338 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1338  in
             uu____1329 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1328
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1393;_})
           ->
           let uu____1408 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1408
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1410;_})
           ->
           let uu____1425 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1425
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1443 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1473 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1491  ->
                                 match uu____1491 with
                                 | (t1,uu____1497) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1473
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1443 (FStar_String.concat "\\/")  in
           let uu____1502 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1502
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1514 = tag_of_term t  in
           let uu____1515 = sli m  in
           let uu____1516 = term_to_string t'  in
           let uu____1517 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1514 uu____1515
             uu____1516 uu____1517
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1530 = tag_of_term t  in
           let uu____1531 = term_to_string t'  in
           let uu____1532 = sli m0  in
           let uu____1533 = sli m1  in
           let uu____1534 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1530
             uu____1531 uu____1532 uu____1533 uu____1534
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1543 = FStar_Range.string_of_range r  in
           let uu____1544 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1543
             uu____1544
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1551 = lid_to_string l  in
           let uu____1552 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1553 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1551 uu____1552
             uu____1553
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1555) ->
           let uu____1560 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1560
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1562 = db_to_string x3  in
           let uu____1563 =
             let uu____1564 =
               let uu____1565 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1565 ")"  in
             Prims.strcat ":(" uu____1564  in
           Prims.strcat uu____1562 uu____1563
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1569) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1596 = FStar_Options.print_universes ()  in
           if uu____1596
           then
             let uu____1597 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1597
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1617 = binders_to_string " -> " bs  in
           let uu____1618 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1617 uu____1618
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1643 = binders_to_string " " bs  in
                let uu____1644 = term_to_string t2  in
                let uu____1645 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1649 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1649)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1643 uu____1644
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1645
            | uu____1652 ->
                let uu____1655 = binders_to_string " " bs  in
                let uu____1656 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1655 uu____1656)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1663 = bv_to_string xt  in
           let uu____1664 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1667 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1663 uu____1664 uu____1667
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1692 = term_to_string t  in
           let uu____1693 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1692 uu____1693
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1712 = lbs_to_string [] lbs  in
           let uu____1713 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1712 uu____1713
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1774 =
                   let uu____1775 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1775
                     (FStar_Util.dflt "default")
                    in
                 let uu____1780 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1774 uu____1780
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1796 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1796
              in
           let uu____1797 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1797 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1836 = term_to_string head1  in
           let uu____1837 =
             let uu____1838 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1874  ->
                       match uu____1874 with
                       | (p,wopt,e) ->
                           let uu____1890 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1891 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1893 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1893
                              in
                           let uu____1894 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1890
                             uu____1891 uu____1894))
                in
             FStar_Util.concat_l "\n\t|" uu____1838  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1836 uu____1837
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1901 = FStar_Options.print_universes ()  in
           if uu____1901
           then
             let uu____1902 = term_to_string t  in
             let uu____1903 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1902 uu____1903
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1906 =
      let uu____1907 = FStar_Options.ugly ()  in Prims.op_Negation uu____1907
       in
    if uu____1906
    then
      let e =
        let uu____1909 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1909  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1932 = fv_to_string l  in
           let uu____1933 =
             let uu____1934 =
               FStar_List.map
                 (fun uu____1945  ->
                    match uu____1945 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1934 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1932 uu____1933
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1957) ->
           let uu____1962 = FStar_Options.print_bound_var_types ()  in
           if uu____1962
           then
             let uu____1963 = bv_to_string x1  in
             let uu____1964 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1963 uu____1964
           else
             (let uu____1966 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1966)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1968 = FStar_Options.print_bound_var_types ()  in
           if uu____1968
           then
             let uu____1969 = bv_to_string x1  in
             let uu____1970 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1969 uu____1970
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1974 = FStar_Options.print_real_names ()  in
           if uu____1974
           then
             let uu____1975 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1975
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1987 = quals_to_string' quals  in
      let uu____1988 =
        let uu____1989 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2005 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2006 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2007 =
                    let uu____2008 = FStar_Options.print_universes ()  in
                    if uu____2008
                    then
                      let uu____2009 =
                        let uu____2010 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2010 ">"  in
                      Prims.strcat "<" uu____2009
                    else ""  in
                  let uu____2012 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2013 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2005
                    uu____2006 uu____2007 uu____2012 uu____2013))
           in
        FStar_Util.concat_l "\n and " uu____1989  in
      FStar_Util.format3 "%slet %s %s" uu____1987
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1988

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___99_2019  ->
    match uu___99_2019 with
    | [] -> ""
    | tms ->
        let uu____2025 =
          let uu____2026 =
            FStar_List.map
              (fun t  ->
                 let uu____2032 = term_to_string t  in paren uu____2032) tms
             in
          FStar_All.pipe_right uu____2026 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2025

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2036 = FStar_Options.print_effect_args ()  in
    if uu____2036
    then
      let uu____2037 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2037
    else
      (let uu____2039 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2040 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2039 uu____2040)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___100_2041  ->
    match uu___100_2041 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2042 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2045 = aqual_to_string aq  in Prims.strcat uu____2045 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
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
             let uu____2059 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2059
             then
               let uu____2060 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2060
             else
               (let uu____2062 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2064 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2064)
                   in
                if uu____2062
                then
                  let uu____2065 = nm_to_string a  in
                  imp_to_string uu____2065 imp
                else
                  (let uu____2067 =
                     let uu____2068 = nm_to_string a  in
                     let uu____2069 =
                       let uu____2070 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2070  in
                     Prims.strcat uu____2068 uu____2069  in
                   imp_to_string uu____2067 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2076 = FStar_Options.print_implicits ()  in
        if uu____2076 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2078 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2078 (FStar_String.concat sep)
      else
        (let uu____2086 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2086 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___101_2093  ->
    match uu___101_2093 with
    | (a,imp) ->
        let uu____2100 = term_to_string a  in imp_to_string uu____2100 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2103 = FStar_Options.print_implicits ()  in
      if uu____2103 then args else filter_imp args  in
    let uu____2107 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2107 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2120 = FStar_Options.ugly ()  in
      if uu____2120
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2125 =
      let uu____2126 = FStar_Options.ugly ()  in Prims.op_Negation uu____2126
       in
    if uu____2125
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2140 =
             let uu____2141 = FStar_Syntax_Subst.compress t  in
             uu____2141.FStar_Syntax_Syntax.n  in
           (match uu____2140 with
            | FStar_Syntax_Syntax.Tm_type uu____2144 when
                let uu____2145 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2145 -> term_to_string t
            | uu____2146 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2148 = univ_to_string u  in
                     let uu____2149 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2148 uu____2149
                 | uu____2150 ->
                     let uu____2153 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2153))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2164 =
             let uu____2165 = FStar_Syntax_Subst.compress t  in
             uu____2165.FStar_Syntax_Syntax.n  in
           (match uu____2164 with
            | FStar_Syntax_Syntax.Tm_type uu____2168 when
                let uu____2169 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2169 -> term_to_string t
            | uu____2170 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2172 = univ_to_string u  in
                     let uu____2173 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2172 uu____2173
                 | uu____2174 ->
                     let uu____2177 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2177))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2180 = FStar_Options.print_effect_args ()  in
             if uu____2180
             then
               let uu____2181 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2182 =
                 let uu____2183 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2183 (FStar_String.concat ", ")
                  in
               let uu____2190 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2191 =
                 let uu____2192 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2192 (FStar_String.concat ", ")
                  in
               let uu____2211 =
                 let uu____2212 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2212 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2181
                 uu____2182 uu____2190 uu____2191 uu____2211
             else
               (let uu____2222 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___102_2226  ->
                           match uu___102_2226 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2227 -> false)))
                    &&
                    (let uu____2229 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2229)
                   in
                if uu____2222
                then
                  let uu____2230 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2230
                else
                  (let uu____2232 =
                     ((let uu____2235 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2235) &&
                        (let uu____2237 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2237))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2232
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2239 =
                        (let uu____2242 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2242) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___103_2246  ->
                                   match uu___103_2246 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2247 -> false)))
                         in
                      if uu____2239
                      then
                        let uu____2248 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2248
                      else
                        (let uu____2250 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2251 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2250 uu____2251))))
              in
           let dec =
             let uu____2253 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___104_2263  ->
                       match uu___104_2263 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2269 =
                             let uu____2270 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2270
                              in
                           [uu____2269]
                       | uu____2271 -> []))
                in
             FStar_All.pipe_right uu____2253 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2275 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___105_2281  ->
    match uu___105_2281 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2294 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2324 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2342  ->
                              match uu____2342 with
                              | (t,uu____2348) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2324
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2294 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2354 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2354
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2357) ->
        let uu____2358 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2358
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2366 = sli m  in
        let uu____2367 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2366 uu____2367
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2375 = sli m  in
        let uu____2376 = sli m'  in
        let uu____2377 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2375
          uu____2376 uu____2377

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2388 = FStar_Options.ugly ()  in
      if uu____2388
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
      let uu____2402 = b  in
      match uu____2402 with
      | (a,imp) ->
          let n1 =
            let uu____2406 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2406
            then FStar_Util.JsonNull
            else
              (let uu____2408 =
                 let uu____2409 = nm_to_string a  in
                 imp_to_string uu____2409 imp  in
               FStar_Util.JsonStr uu____2408)
             in
          let t =
            let uu____2411 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2411  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2434 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2434
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2442 = FStar_Options.print_universes ()  in
    if uu____2442 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2449 =
      let uu____2450 = FStar_Options.ugly ()  in Prims.op_Negation uu____2450
       in
    if uu____2449
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2454 = s  in
       match uu____2454 with
       | (us,t) ->
           let uu____2461 =
             let uu____2462 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2462  in
           let uu____2463 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2461 uu____2463)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2469 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2470 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2471 =
      let uu____2472 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2472  in
    let uu____2473 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2474 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2469 uu____2470 uu____2471
      uu____2473 uu____2474
  
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
          let uu____2499 =
            let uu____2500 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2500  in
          if uu____2499
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2514 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2514 (FStar_String.concat ",\n\t")
                in
             let uu____2523 =
               let uu____2526 =
                 let uu____2529 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2530 =
                   let uu____2533 =
                     let uu____2534 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2534  in
                   let uu____2535 =
                     let uu____2538 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2539 =
                       let uu____2542 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2543 =
                         let uu____2546 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2547 =
                           let uu____2550 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2551 =
                             let uu____2554 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2555 =
                               let uu____2558 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2559 =
                                 let uu____2562 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2563 =
                                   let uu____2566 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2567 =
                                     let uu____2570 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2571 =
                                       let uu____2574 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2575 =
                                         let uu____2578 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2579 =
                                           let uu____2582 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2583 =
                                             let uu____2586 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2587 =
                                               let uu____2590 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2591 =
                                                 let uu____2594 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2595 =
                                                   let uu____2598 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2598]  in
                                                 uu____2594 :: uu____2595  in
                                               uu____2590 :: uu____2591  in
                                             uu____2586 :: uu____2587  in
                                           uu____2582 :: uu____2583  in
                                         uu____2578 :: uu____2579  in
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
                   uu____2533 :: uu____2535  in
                 uu____2529 :: uu____2530  in
               (if for_free then "_for_free " else "") :: uu____2526  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2523)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2615 =
      let uu____2616 = FStar_Options.ugly ()  in Prims.op_Negation uu____2616
       in
    if uu____2615
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2622 -> ""
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
             (lid,univs1,tps,k,uu____2633,uu____2634) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2646 = FStar_Options.print_universes ()  in
             if uu____2646
             then
               let uu____2647 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2647 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2652,uu____2653,uu____2654) ->
             let uu____2659 = FStar_Options.print_universes ()  in
             if uu____2659
             then
               let uu____2660 = univ_names_to_string univs1  in
               let uu____2661 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2660
                 lid.FStar_Ident.str uu____2661
             else
               (let uu____2663 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2663)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2667 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2668 =
               let uu____2669 = FStar_Options.print_universes ()  in
               if uu____2669
               then
                 let uu____2670 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2670
               else ""  in
             let uu____2672 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2667
               lid.FStar_Ident.str uu____2668 uu____2672
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2674,f) ->
             let uu____2676 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2676
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2678) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2684 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2684
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2686) ->
             let uu____2695 =
               let uu____2696 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2696 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2695
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2714) -> lift_wp
               | (uu____2721,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2729 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2729 with
              | (us,t) ->
                  let uu____2740 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2741 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2742 = univ_names_to_string us  in
                  let uu____2743 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2740 uu____2741 uu____2742 uu____2743)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2753 = FStar_Options.print_universes ()  in
             if uu____2753
             then
               let uu____2754 =
                 let uu____2759 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2759  in
               (match uu____2754 with
                | (univs2,t) ->
                    let uu____2762 =
                      let uu____2775 =
                        let uu____2776 = FStar_Syntax_Subst.compress t  in
                        uu____2776.FStar_Syntax_Syntax.n  in
                      match uu____2775 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2817 -> failwith "impossible"  in
                    (match uu____2762 with
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
        let uu____2924 = lbname_to_string lb  in
        let uu____2925 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2924 uu____2925
    | uu____2926 ->
        let uu____2927 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2927 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2943 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2944 =
      let uu____2945 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2945 (FStar_String.concat "\n")  in
    let uu____2950 =
      let uu____2951 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2951 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2943 uu____2944 uu____2950
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___106_2960  ->
    match uu___106_2960 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2963 = FStar_Util.string_of_int i  in
        let uu____2964 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2963 uu____2964
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2967 = bv_to_string x  in
        let uu____2968 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2967 uu____2968
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2975 = bv_to_string x  in
        let uu____2976 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2975 uu____2976
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2979 = FStar_Util.string_of_int i  in
        let uu____2980 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2979 uu____2980
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2983 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2983
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2989 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2989 (FStar_String.concat "; ")
  
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
          (let uu____3025 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3025))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3032 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3032)));
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
           (let uu____3066 = f x  in
            FStar_Util.string_builder_append strb uu____3066);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3073 = f x1  in
                 FStar_Util.string_builder_append strb uu____3073)) xs;
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
           (let uu____3111 = f x  in
            FStar_Util.string_builder_append strb uu____3111);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3118 = f x1  in
                 FStar_Util.string_builder_append strb uu____3118)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3134 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3134
  