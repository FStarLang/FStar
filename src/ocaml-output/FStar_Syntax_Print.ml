open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___201_5  ->
    match uu___201_5 with
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
  fun uu___202_281  ->
    match uu___202_281 with
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
         (fun uu___203_347  ->
            match uu___203_347 with
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
        let uu____436 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____436
        then
          let uu____441 =
            let uu____446 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____446  in
          (match uu____441 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____456 =
                 let uu____459 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____459 :: xs  in
               FStar_Pervasives_Native.Some uu____456
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____469 ->
        let uu____470 = is_lex_top e  in
        if uu____470
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____511 = f hd1  in if uu____511 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____535 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____535
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____559 = get_lid e  in find_lid uu____559 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____569 = get_lid e  in find_lid uu____569 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____579 = get_lid t  in find_lid uu____579 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___204_589  ->
    match uu___204_589 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____597 = FStar_Options.hide_uvar_nums ()  in
    if uu____597
    then "?"
    else
      (let uu____599 =
         let uu____600 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____600 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____599)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____606 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____607 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____606 uu____607
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
     FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun u  ->
    let uu____629 = FStar_Options.hide_uvar_nums ()  in
    if uu____629
    then "?"
    else
      (let uu____631 =
         let uu____632 =
           let uu____633 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____633 FStar_Util.string_of_int  in
         let uu____634 =
           let uu____635 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____635  in
         Prims.strcat uu____632 uu____634  in
       Prims.strcat "?" uu____631)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____656 = FStar_Syntax_Subst.compress_univ u  in
      match uu____656 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____666 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____674 =
      let uu____675 = FStar_Options.ugly ()  in Prims.op_Negation uu____675
       in
    if uu____674
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____679 = FStar_Syntax_Subst.compress_univ u  in
       match uu____679 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____691 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____691
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____693 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____693 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____707 = univ_to_string u2  in
                let uu____708 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____707 uu____708)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____712 =
             let uu____713 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____713 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____712
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____727 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____727 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____737 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____737 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___205_748  ->
    match uu___205_748 with
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
        let uu____750 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____750
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____753 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____753 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____764 =
          let uu____765 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____765  in
        let uu____766 =
          let uu____767 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____767 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____764 uu____766
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____786 =
          let uu____787 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____787  in
        let uu____788 =
          let uu____789 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____789 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____786 uu____788
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____799 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____799
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
    | uu____810 ->
        let uu____813 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____813 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____831 ->
        let uu____834 = quals_to_string quals  in Prims.strcat uu____834 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____978 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____978
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____980 = nm_to_string x  in Prims.strcat "Tm_name: " uu____980
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____982 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____982
    | FStar_Syntax_Syntax.Tm_uinst uu____983 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____990 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____991 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____992,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____993;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1008,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1009;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1024 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1043 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1058 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1065 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1082 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1105 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1132 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1145 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1158,m) ->
        let uu____1196 = FStar_ST.op_Bang m  in
        (match uu____1196 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1252 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1257,m) ->
        let uu____1263 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1263
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1264 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1266 =
      let uu____1267 = FStar_Options.ugly ()  in Prims.op_Negation uu____1267
       in
    if uu____1266
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1275 = FStar_Options.print_implicits ()  in
         if uu____1275 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1279 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1302,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1326 =
             let uu____1327 =
               let uu____1328 =
                 let uu____1329 =
                   let uu____1338 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1338  in
                 uu____1329 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1328  in
             Prims.strcat uu____1327 "]"  in
           Prims.strcat "[lazy:" uu____1326
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1389;_})
           ->
           let uu____1404 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1404
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1406;_})
           ->
           let uu____1421 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1421
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1441 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1475 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1497  ->
                                 match uu____1497 with
                                 | (t1,uu____1505) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1475
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1441 (FStar_String.concat "\\/")  in
           let uu____1514 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1514
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1526 = tag_of_term t  in
           let uu____1527 = sli m  in
           let uu____1528 = term_to_string t'  in
           let uu____1529 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1526 uu____1527
             uu____1528 uu____1529
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1542 = tag_of_term t  in
           let uu____1543 = term_to_string t'  in
           let uu____1544 = sli m0  in
           let uu____1545 = sli m1  in
           let uu____1546 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1542
             uu____1543 uu____1544 uu____1545 uu____1546
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1555 = FStar_Range.string_of_range r  in
           let uu____1556 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1555
             uu____1556
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1563 = lid_to_string l  in
           let uu____1564 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1565 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1563 uu____1564
             uu____1565
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1567) ->
           let uu____1572 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1572
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1574 = db_to_string x3  in
           let uu____1575 =
             let uu____1576 =
               let uu____1577 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1577 ")"  in
             Prims.strcat ":(" uu____1576  in
           Prims.strcat uu____1574 uu____1575
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1581)) ->
           let uu____1596 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1596
           then ctx_uvar_to_string u
           else
             (let uu____1598 =
                let uu____1599 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1599  in
              Prims.strcat "?" uu____1598)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1618 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1618
           then
             let uu____1619 = ctx_uvar_to_string u  in
             let uu____1620 =
               let uu____1621 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1621 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1619 uu____1620
           else
             (let uu____1633 =
                let uu____1634 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1634  in
              Prims.strcat "?" uu____1633)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1637 = FStar_Options.print_universes ()  in
           if uu____1637
           then
             let uu____1638 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1638
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1662 = binders_to_string " -> " bs  in
           let uu____1663 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1662 uu____1663
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1692 = binders_to_string " " bs  in
                let uu____1693 = term_to_string t2  in
                let uu____1694 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1698 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1698)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1692 uu____1693
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1694
            | uu____1701 ->
                let uu____1704 = binders_to_string " " bs  in
                let uu____1705 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1704 uu____1705)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1712 = bv_to_string xt  in
           let uu____1713 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1714 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1712 uu____1713 uu____1714
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1743 = term_to_string t  in
           let uu____1744 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1743 uu____1744
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1763 = lbs_to_string [] lbs  in
           let uu____1764 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1763 uu____1764
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1825 =
                   let uu____1826 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1826
                     (FStar_Util.dflt "default")
                    in
                 let uu____1831 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1825 uu____1831
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1847 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1847
              in
           let uu____1848 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1848 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1887 = term_to_string head1  in
           let uu____1888 =
             let uu____1889 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1919  ->
                       match uu____1919 with
                       | (p,wopt,e) ->
                           let uu____1935 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1936 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1938 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1938
                              in
                           let uu____1939 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1935
                             uu____1936 uu____1939))
                in
             FStar_Util.concat_l "\n\t|" uu____1889  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1887 uu____1888
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1946 = FStar_Options.print_universes ()  in
           if uu____1946
           then
             let uu____1947 = term_to_string t  in
             let uu____1948 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1947 uu____1948
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____1951 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____1952 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____1953 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____1951 uu____1952
      uu____1953

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___206_1954  ->
    match uu___206_1954 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____1957 = FStar_Util.string_of_int i  in
        let uu____1958 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____1957 uu____1958
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____1961 = bv_to_string x  in
        let uu____1962 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____1961 uu____1962
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____1969 = bv_to_string x  in
        let uu____1970 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____1969 uu____1970
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____1973 = FStar_Util.string_of_int i  in
        let uu____1974 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____1973 uu____1974
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____1977 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____1977

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____1979 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____1979 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1989 =
      let uu____1990 = FStar_Options.ugly ()  in Prims.op_Negation uu____1990
       in
    if uu____1989
    then
      let e =
        let uu____1992 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1992  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2015 = fv_to_string l  in
           let uu____2016 =
             let uu____2017 =
               FStar_List.map
                 (fun uu____2028  ->
                    match uu____2028 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2017 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2015 uu____2016
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2040) ->
           let uu____2045 = FStar_Options.print_bound_var_types ()  in
           if uu____2045
           then
             let uu____2046 = bv_to_string x1  in
             let uu____2047 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2046 uu____2047
           else
             (let uu____2049 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2049)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2051 = FStar_Options.print_bound_var_types ()  in
           if uu____2051
           then
             let uu____2052 = bv_to_string x1  in
             let uu____2053 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2052 uu____2053
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2057 = FStar_Options.print_real_names ()  in
           if uu____2057
           then
             let uu____2058 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2058
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2070 = quals_to_string' quals  in
      let uu____2071 =
        let uu____2072 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2088 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2089 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2090 =
                    let uu____2091 = FStar_Options.print_universes ()  in
                    if uu____2091
                    then
                      let uu____2092 =
                        let uu____2093 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2093 ">"  in
                      Prims.strcat "<" uu____2092
                    else ""  in
                  let uu____2095 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2096 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2088
                    uu____2089 uu____2090 uu____2095 uu____2096))
           in
        FStar_Util.concat_l "\n and " uu____2072  in
      FStar_Util.format3 "%slet %s %s" uu____2070
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2071

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___207_2100  ->
    match uu___207_2100 with
    | [] -> ""
    | tms ->
        let uu____2106 =
          let uu____2107 =
            FStar_List.map
              (fun t  ->
                 let uu____2113 = term_to_string t  in paren uu____2113) tms
             in
          FStar_All.pipe_right uu____2107 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2106

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2117 = FStar_Options.print_effect_args ()  in
    if uu____2117
    then
      let uu____2118 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2118
    else
      (let uu____2120 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2121 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2120 uu____2121)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___208_2122  ->
    match uu___208_2122 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2123 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2126 = aqual_to_string aq  in Prims.strcat uu____2126 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2135 =
        let uu____2136 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2136  in
      if uu____2135
      then
        let uu____2137 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2137 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2143 = b  in
         match uu____2143 with
         | (a,imp) ->
             let uu____2156 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2156
             then
               let uu____2157 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2157
             else
               (let uu____2159 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2161 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2161)
                   in
                if uu____2159
                then
                  let uu____2162 = nm_to_string a  in
                  imp_to_string uu____2162 imp
                else
                  (let uu____2164 =
                     let uu____2165 = nm_to_string a  in
                     let uu____2166 =
                       let uu____2167 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2167  in
                     Prims.strcat uu____2165 uu____2166  in
                   imp_to_string uu____2164 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  = fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2181 = FStar_Options.print_implicits ()  in
        if uu____2181 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2185 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2185 (FStar_String.concat sep)
      else
        (let uu____2207 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2207 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___209_2216  ->
    match uu___209_2216 with
    | (a,imp) ->
        let uu____2223 = term_to_string a  in imp_to_string uu____2223 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2232 = FStar_Options.print_implicits ()  in
      if uu____2232 then args else filter_imp args  in
    let uu____2242 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2242 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2261 = FStar_Options.ugly ()  in
      if uu____2261
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2266 =
      let uu____2267 = FStar_Options.ugly ()  in Prims.op_Negation uu____2267
       in
    if uu____2266
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2281 =
             let uu____2282 = FStar_Syntax_Subst.compress t  in
             uu____2282.FStar_Syntax_Syntax.n  in
           (match uu____2281 with
            | FStar_Syntax_Syntax.Tm_type uu____2285 when
                let uu____2286 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2286 -> term_to_string t
            | uu____2287 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2289 = univ_to_string u  in
                     let uu____2290 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2289 uu____2290
                 | uu____2291 ->
                     let uu____2294 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2294))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2305 =
             let uu____2306 = FStar_Syntax_Subst.compress t  in
             uu____2306.FStar_Syntax_Syntax.n  in
           (match uu____2305 with
            | FStar_Syntax_Syntax.Tm_type uu____2309 when
                let uu____2310 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2310 -> term_to_string t
            | uu____2311 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2313 = univ_to_string u  in
                     let uu____2314 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2313 uu____2314
                 | uu____2315 ->
                     let uu____2318 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2318))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2321 = FStar_Options.print_effect_args ()  in
             if uu____2321
             then
               let uu____2322 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2323 =
                 let uu____2324 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2324 (FStar_String.concat ", ")
                  in
               let uu____2333 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2334 =
                 let uu____2335 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2335 (FStar_String.concat ", ")
                  in
               let uu____2352 =
                 let uu____2353 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2353 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2322
                 uu____2323 uu____2333 uu____2334 uu____2352
             else
               (let uu____2363 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_2367  ->
                           match uu___210_2367 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2368 -> false)))
                    &&
                    (let uu____2370 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2370)
                   in
                if uu____2363
                then
                  let uu____2371 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2371
                else
                  (let uu____2373 =
                     ((let uu____2376 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2376) &&
                        (let uu____2378 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2378))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2373
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2380 =
                        (let uu____2383 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2383) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2387  ->
                                   match uu___211_2387 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2388 -> false)))
                         in
                      if uu____2380
                      then
                        let uu____2389 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2389
                      else
                        (let uu____2391 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2392 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2391 uu____2392))))
              in
           let dec =
             let uu____2394 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2404  ->
                       match uu___212_2404 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2410 =
                             let uu____2411 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2411
                              in
                           [uu____2410]
                       | uu____2412 -> []))
                in
             FStar_All.pipe_right uu____2394 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2416 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___213_2422  ->
    match uu___213_2422 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2437 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2471 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2493  ->
                              match uu____2493 with
                              | (t,uu____2501) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2471
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2437 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2511 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2511
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2514) ->
        let uu____2515 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2515
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2523 = sli m  in
        let uu____2524 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2523 uu____2524
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2532 = sli m  in
        let uu____2533 = sli m'  in
        let uu____2534 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2532
          uu____2533 uu____2534

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2545 = FStar_Options.ugly ()  in
      if uu____2545
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
      let uu____2559 = b  in
      match uu____2559 with
      | (a,imp) ->
          let n1 =
            let uu____2567 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2567
            then FStar_Util.JsonNull
            else
              (let uu____2569 =
                 let uu____2570 = nm_to_string a  in
                 imp_to_string uu____2570 imp  in
               FStar_Util.JsonStr uu____2569)
             in
          let t =
            let uu____2572 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2572  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2595 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2595
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2609 = FStar_Options.print_universes ()  in
    if uu____2609 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2616 =
      let uu____2617 = FStar_Options.ugly ()  in Prims.op_Negation uu____2617
       in
    if uu____2616
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2621 = s  in
       match uu____2621 with
       | (us,t) ->
           let uu____2632 =
             let uu____2633 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2633  in
           let uu____2634 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2632 uu____2634)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2640 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2641 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2642 =
      let uu____2643 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2643  in
    let uu____2644 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2645 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2640 uu____2641 uu____2642
      uu____2644 uu____2645
  
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
          let uu____2670 =
            let uu____2671 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2671  in
          if uu____2670
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2685 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2685 (FStar_String.concat ",\n\t")
                in
             let uu____2694 =
               let uu____2697 =
                 let uu____2700 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2701 =
                   let uu____2704 =
                     let uu____2705 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2705  in
                   let uu____2706 =
                     let uu____2709 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2710 =
                       let uu____2713 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2714 =
                         let uu____2717 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2718 =
                           let uu____2721 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2722 =
                             let uu____2725 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2726 =
                               let uu____2729 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2730 =
                                 let uu____2733 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2734 =
                                   let uu____2737 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2738 =
                                     let uu____2741 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2742 =
                                       let uu____2745 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2746 =
                                         let uu____2749 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2750 =
                                           let uu____2753 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2754 =
                                             let uu____2757 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2758 =
                                               let uu____2761 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2762 =
                                                 let uu____2765 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2766 =
                                                   let uu____2769 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2769]  in
                                                 uu____2765 :: uu____2766  in
                                               uu____2761 :: uu____2762  in
                                             uu____2757 :: uu____2758  in
                                           uu____2753 :: uu____2754  in
                                         uu____2749 :: uu____2750  in
                                       uu____2745 :: uu____2746  in
                                     uu____2741 :: uu____2742  in
                                   uu____2737 :: uu____2738  in
                                 uu____2733 :: uu____2734  in
                               uu____2729 :: uu____2730  in
                             uu____2725 :: uu____2726  in
                           uu____2721 :: uu____2722  in
                         uu____2717 :: uu____2718  in
                       uu____2713 :: uu____2714  in
                     uu____2709 :: uu____2710  in
                   uu____2704 :: uu____2706  in
                 uu____2700 :: uu____2701  in
               (if for_free then "_for_free " else "") :: uu____2697  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2694)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2786 =
      let uu____2787 = FStar_Options.ugly ()  in Prims.op_Negation uu____2787
       in
    if uu____2786
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2793 -> ""
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
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
             (FStar_Pervasives_Native.None )) -> "#push-options"
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
             (FStar_Pervasives_Native.Some s)) ->
             FStar_Util.format1 "#push-options \"%s\"" s
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions )
             -> "#pop-options"
         | FStar_Syntax_Syntax.Sig_inductive_typ
             (lid,univs1,tps,k,uu____2805,uu____2806) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2818 = FStar_Options.print_universes ()  in
             if uu____2818
             then
               let uu____2819 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2819 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2824,uu____2825,uu____2826) ->
             let uu____2831 = FStar_Options.print_universes ()  in
             if uu____2831
             then
               let uu____2832 = univ_names_to_string univs1  in
               let uu____2833 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2832
                 lid.FStar_Ident.str uu____2833
             else
               (let uu____2835 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2835)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2839 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2840 =
               let uu____2841 = FStar_Options.print_universes ()  in
               if uu____2841
               then
                 let uu____2842 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2842
               else ""  in
             let uu____2844 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2839
               lid.FStar_Ident.str uu____2840 uu____2844
         | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
             let uu____2848 = FStar_Options.print_universes ()  in
             if uu____2848
             then
               let uu____2849 = univ_names_to_string us  in
               let uu____2850 = term_to_string f  in
               FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
                 uu____2849 uu____2850
             else
               (let uu____2852 = term_to_string f  in
                FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str
                  uu____2852)
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2854) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2860 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2860
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2862) ->
             let uu____2871 =
               let uu____2872 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2872 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2871
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2908) -> lift_wp
               | (uu____2915,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2923 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2923 with
              | (us,t) ->
                  let uu____2934 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2935 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2936 = univ_names_to_string us  in
                  let uu____2937 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2934 uu____2935 uu____2936 uu____2937)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2947 = FStar_Options.print_universes ()  in
             if uu____2947
             then
               let uu____2948 =
                 let uu____2953 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2953  in
               (match uu____2948 with
                | (univs2,t) ->
                    let uu____2966 =
                      let uu____2971 =
                        let uu____2972 = FStar_Syntax_Subst.compress t  in
                        uu____2972.FStar_Syntax_Syntax.n  in
                      match uu____2971 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____3001 -> failwith "impossible"  in
                    (match uu____2966 with
                     | (tps1,c1) ->
                         let uu____3008 = sli l  in
                         let uu____3009 = univ_names_to_string univs2  in
                         let uu____3010 = binders_to_string " " tps1  in
                         let uu____3011 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____3008 uu____3009 uu____3010 uu____3011))
             else
               (let uu____3013 = sli l  in
                let uu____3014 = binders_to_string " " tps  in
                let uu____3015 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____3013 uu____3014
                  uu____3015)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____3022 =
               let uu____3023 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____3023  in
             let uu____3028 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____3022 uu____3028
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____3029 ->
           let uu____3032 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____3032 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3043 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3043 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3049,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3051;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3053;
                       FStar_Syntax_Syntax.lbdef = uu____3054;
                       FStar_Syntax_Syntax.lbattrs = uu____3055;
                       FStar_Syntax_Syntax.lbpos = uu____3056;_}::[]),uu____3057)
        ->
        let uu____3078 = lbname_to_string lb  in
        let uu____3079 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3078 uu____3079
    | uu____3080 ->
        let uu____3081 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3081 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3097 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3098 =
      let uu____3099 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3099 (FStar_String.concat "\n")  in
    let uu____3104 =
      let uu____3105 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3105 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3097 uu____3098 uu____3104
  
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
          (let uu____3139 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3139))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3146 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3146)));
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
           (let uu____3180 = f x  in
            FStar_Util.string_builder_append strb uu____3180);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3187 = f x1  in
                 FStar_Util.string_builder_append strb uu____3187)) xs;
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
           (let uu____3225 = f x  in
            FStar_Util.string_builder_append strb uu____3225);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3232 = f x1  in
                 FStar_Util.string_builder_append strb uu____3232)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3248 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3248
  