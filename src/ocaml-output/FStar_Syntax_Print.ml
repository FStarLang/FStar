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
         | FStar_Pervasives_Native.Some uu____1256 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1261,m) ->
        let uu____1267 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1267
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1268 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1270 =
      let uu____1271 = FStar_Options.ugly ()  in Prims.op_Negation uu____1271
       in
    if uu____1270
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1279 = FStar_Options.print_implicits ()  in
         if uu____1279 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1283 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1306,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1330,thunk);
             FStar_Syntax_Syntax.ltyp = uu____1332;
             FStar_Syntax_Syntax.rng = uu____1333;_}
           ->
           let uu____1344 = FStar_Common.force_thunk thunk  in
           term_to_string uu____1344
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1388 =
             let uu____1389 =
               let uu____1398 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1398  in
             uu____1389 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1388
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1453;_})
           ->
           let uu____1468 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1468
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1470;_})
           ->
           let uu____1485 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1485
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1505 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1539 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1561  ->
                                 match uu____1561 with
                                 | (t1,uu____1569) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1539
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1505 (FStar_String.concat "\\/")  in
           let uu____1578 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1578
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1590 = tag_of_term t  in
           let uu____1591 = sli m  in
           let uu____1592 = term_to_string t'  in
           let uu____1593 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1590 uu____1591
             uu____1592 uu____1593
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1606 = tag_of_term t  in
           let uu____1607 = term_to_string t'  in
           let uu____1608 = sli m0  in
           let uu____1609 = sli m1  in
           let uu____1610 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1606
             uu____1607 uu____1608 uu____1609 uu____1610
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1619 = FStar_Range.string_of_range r  in
           let uu____1620 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1619
             uu____1620
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1627 = lid_to_string l  in
           let uu____1628 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1629 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1627 uu____1628
             uu____1629
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1631) ->
           let uu____1636 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1636
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1638 = db_to_string x3  in
           let uu____1639 =
             let uu____1640 =
               let uu____1641 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1641 ")"  in
             Prims.strcat ":(" uu____1640  in
           Prims.strcat uu____1638 uu____1639
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1645)) ->
           let uu____1660 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1660
           then ctx_uvar_to_string u
           else
             (let uu____1662 =
                let uu____1663 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1663  in
              Prims.strcat "?" uu____1662)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1682 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1682
           then
             let uu____1683 = ctx_uvar_to_string u  in
             let uu____1684 =
               let uu____1685 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1685 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1683 uu____1684
           else
             (let uu____1697 =
                let uu____1698 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1698  in
              Prims.strcat "?" uu____1697)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1701 = FStar_Options.print_universes ()  in
           if uu____1701
           then
             let uu____1702 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1702
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1726 = binders_to_string " -> " bs  in
           let uu____1727 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1726 uu____1727
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1756 = binders_to_string " " bs  in
                let uu____1757 = term_to_string t2  in
                let uu____1758 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1762 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1762)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1756 uu____1757
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1758
            | uu____1765 ->
                let uu____1768 = binders_to_string " " bs  in
                let uu____1769 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1768 uu____1769)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1776 = bv_to_string xt  in
           let uu____1777 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1778 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1776 uu____1777 uu____1778
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1807 = term_to_string t  in
           let uu____1808 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1807 uu____1808
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1827 = lbs_to_string [] lbs  in
           let uu____1828 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1827 uu____1828
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1889 =
                   let uu____1890 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1890
                     (FStar_Util.dflt "default")
                    in
                 let uu____1895 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1889 uu____1895
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1911 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1911
              in
           let uu____1912 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1912 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1951 = term_to_string head1  in
           let uu____1952 =
             let uu____1953 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1983  ->
                       match uu____1983 with
                       | (p,wopt,e) ->
                           let uu____1999 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____2000 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____2002 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____2002
                              in
                           let uu____2003 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1999
                             uu____2000 uu____2003))
                in
             FStar_Util.concat_l "\n\t|" uu____1953  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1951 uu____1952
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2010 = FStar_Options.print_universes ()  in
           if uu____2010
           then
             let uu____2011 = term_to_string t  in
             let uu____2012 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2011 uu____2012
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2015 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2016 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2017 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2015 uu____2016
      uu____2017

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___206_2018  ->
    match uu___206_2018 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2021 = FStar_Util.string_of_int i  in
        let uu____2022 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2021 uu____2022
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2025 = bv_to_string x  in
        let uu____2026 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2025 uu____2026
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2033 = bv_to_string x  in
        let uu____2034 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2033 uu____2034
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2037 = FStar_Util.string_of_int i  in
        let uu____2038 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2037 uu____2038
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2041 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2041

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2043 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2043 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2053 =
      let uu____2054 = FStar_Options.ugly ()  in Prims.op_Negation uu____2054
       in
    if uu____2053
    then
      let e =
        let uu____2056 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2056  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2079 = fv_to_string l  in
           let uu____2080 =
             let uu____2081 =
               FStar_List.map
                 (fun uu____2092  ->
                    match uu____2092 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2081 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2079 uu____2080
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2104) ->
           let uu____2109 = FStar_Options.print_bound_var_types ()  in
           if uu____2109
           then
             let uu____2110 = bv_to_string x1  in
             let uu____2111 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2110 uu____2111
           else
             (let uu____2113 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2113)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2115 = FStar_Options.print_bound_var_types ()  in
           if uu____2115
           then
             let uu____2116 = bv_to_string x1  in
             let uu____2117 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2116 uu____2117
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2121 = FStar_Options.print_real_names ()  in
           if uu____2121
           then
             let uu____2122 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2122
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2134 = quals_to_string' quals  in
      let uu____2135 =
        let uu____2136 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2152 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2153 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2154 =
                    let uu____2155 = FStar_Options.print_universes ()  in
                    if uu____2155
                    then
                      let uu____2156 =
                        let uu____2157 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2157 ">"  in
                      Prims.strcat "<" uu____2156
                    else ""  in
                  let uu____2159 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2160 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2152
                    uu____2153 uu____2154 uu____2159 uu____2160))
           in
        FStar_Util.concat_l "\n and " uu____2136  in
      FStar_Util.format3 "%slet %s %s" uu____2134
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2135

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___207_2164  ->
    match uu___207_2164 with
    | [] -> ""
    | tms ->
        let uu____2170 =
          let uu____2171 =
            FStar_List.map
              (fun t  ->
                 let uu____2177 = term_to_string t  in paren uu____2177) tms
             in
          FStar_All.pipe_right uu____2171 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2170

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2181 = FStar_Options.print_effect_args ()  in
    if uu____2181
    then
      let uu____2182 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2182
    else
      (let uu____2184 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2185 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2184 uu____2185)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___208_2186  ->
    match uu___208_2186 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2187 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2190 = aqual_to_string aq  in Prims.strcat uu____2190 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2199 =
        let uu____2200 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2200  in
      if uu____2199
      then
        let uu____2201 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2201 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2207 = b  in
         match uu____2207 with
         | (a,imp) ->
             let uu____2220 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2220
             then
               let uu____2221 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2221
             else
               (let uu____2223 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2225 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2225)
                   in
                if uu____2223
                then
                  let uu____2226 = nm_to_string a  in
                  imp_to_string uu____2226 imp
                else
                  (let uu____2228 =
                     let uu____2229 = nm_to_string a  in
                     let uu____2230 =
                       let uu____2231 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2231  in
                     Prims.strcat uu____2229 uu____2230  in
                   imp_to_string uu____2228 imp)))

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
        let uu____2245 = FStar_Options.print_implicits ()  in
        if uu____2245 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2249 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2249 (FStar_String.concat sep)
      else
        (let uu____2271 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2271 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___209_2280  ->
    match uu___209_2280 with
    | (a,imp) ->
        let uu____2287 = term_to_string a  in imp_to_string uu____2287 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2296 = FStar_Options.print_implicits ()  in
      if uu____2296 then args else filter_imp args  in
    let uu____2306 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2306 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2325 = FStar_Options.ugly ()  in
      if uu____2325
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2330 =
      let uu____2331 = FStar_Options.ugly ()  in Prims.op_Negation uu____2331
       in
    if uu____2330
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2345 =
             let uu____2346 = FStar_Syntax_Subst.compress t  in
             uu____2346.FStar_Syntax_Syntax.n  in
           (match uu____2345 with
            | FStar_Syntax_Syntax.Tm_type uu____2349 when
                let uu____2350 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2350 -> term_to_string t
            | uu____2351 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2353 = univ_to_string u  in
                     let uu____2354 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2353 uu____2354
                 | uu____2355 ->
                     let uu____2358 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2358))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2369 =
             let uu____2370 = FStar_Syntax_Subst.compress t  in
             uu____2370.FStar_Syntax_Syntax.n  in
           (match uu____2369 with
            | FStar_Syntax_Syntax.Tm_type uu____2373 when
                let uu____2374 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2374 -> term_to_string t
            | uu____2375 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2377 = univ_to_string u  in
                     let uu____2378 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2377 uu____2378
                 | uu____2379 ->
                     let uu____2382 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2382))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2385 = FStar_Options.print_effect_args ()  in
             if uu____2385
             then
               let uu____2386 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2387 =
                 let uu____2388 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2388 (FStar_String.concat ", ")
                  in
               let uu____2397 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2398 =
                 let uu____2399 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2399 (FStar_String.concat ", ")
                  in
               let uu____2416 =
                 let uu____2417 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2417 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2386
                 uu____2387 uu____2397 uu____2398 uu____2416
             else
               (let uu____2427 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_2431  ->
                           match uu___210_2431 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2432 -> false)))
                    &&
                    (let uu____2434 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2434)
                   in
                if uu____2427
                then
                  let uu____2435 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2435
                else
                  (let uu____2437 =
                     ((let uu____2440 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2440) &&
                        (let uu____2442 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2442))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2437
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2444 =
                        (let uu____2447 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2447) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2451  ->
                                   match uu___211_2451 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2452 -> false)))
                         in
                      if uu____2444
                      then
                        let uu____2453 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2453
                      else
                        (let uu____2455 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2456 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2455 uu____2456))))
              in
           let dec =
             let uu____2458 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2468  ->
                       match uu___212_2468 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2474 =
                             let uu____2475 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2475
                              in
                           [uu____2474]
                       | uu____2476 -> []))
                in
             FStar_All.pipe_right uu____2458 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2480 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___213_2486  ->
    match uu___213_2486 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2501 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2535 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2557  ->
                              match uu____2557 with
                              | (t,uu____2565) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2535
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2501 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2575 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2575
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2578) ->
        let uu____2579 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2579
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2587 = sli m  in
        let uu____2588 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2587 uu____2588
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2596 = sli m  in
        let uu____2597 = sli m'  in
        let uu____2598 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2596
          uu____2597 uu____2598

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2609 = FStar_Options.ugly ()  in
      if uu____2609
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
      let uu____2623 = b  in
      match uu____2623 with
      | (a,imp) ->
          let n1 =
            let uu____2631 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2631
            then FStar_Util.JsonNull
            else
              (let uu____2633 =
                 let uu____2634 = nm_to_string a  in
                 imp_to_string uu____2634 imp  in
               FStar_Util.JsonStr uu____2633)
             in
          let t =
            let uu____2636 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2636  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2659 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2659
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2673 = FStar_Options.print_universes ()  in
    if uu____2673 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2680 =
      let uu____2681 = FStar_Options.ugly ()  in Prims.op_Negation uu____2681
       in
    if uu____2680
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2685 = s  in
       match uu____2685 with
       | (us,t) ->
           let uu____2696 =
             let uu____2697 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2697  in
           let uu____2698 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2696 uu____2698)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2704 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2705 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2706 =
      let uu____2707 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2707  in
    let uu____2708 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2709 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2704 uu____2705 uu____2706
      uu____2708 uu____2709
  
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
          let uu____2734 =
            let uu____2735 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2735  in
          if uu____2734
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2749 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2749 (FStar_String.concat ",\n\t")
                in
             let uu____2758 =
               let uu____2761 =
                 let uu____2764 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2765 =
                   let uu____2768 =
                     let uu____2769 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2769  in
                   let uu____2770 =
                     let uu____2773 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2774 =
                       let uu____2777 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2778 =
                         let uu____2781 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2782 =
                           let uu____2785 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2786 =
                             let uu____2789 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2790 =
                               let uu____2793 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2794 =
                                 let uu____2797 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2798 =
                                   let uu____2801 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2802 =
                                     let uu____2805 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2806 =
                                       let uu____2809 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2810 =
                                         let uu____2813 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2814 =
                                           let uu____2817 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2818 =
                                             let uu____2821 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2822 =
                                               let uu____2825 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2826 =
                                                 let uu____2829 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2830 =
                                                   let uu____2833 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2833]  in
                                                 uu____2829 :: uu____2830  in
                                               uu____2825 :: uu____2826  in
                                             uu____2821 :: uu____2822  in
                                           uu____2817 :: uu____2818  in
                                         uu____2813 :: uu____2814  in
                                       uu____2809 :: uu____2810  in
                                     uu____2805 :: uu____2806  in
                                   uu____2801 :: uu____2802  in
                                 uu____2797 :: uu____2798  in
                               uu____2793 :: uu____2794  in
                             uu____2789 :: uu____2790  in
                           uu____2785 :: uu____2786  in
                         uu____2781 :: uu____2782  in
                       uu____2777 :: uu____2778  in
                     uu____2773 :: uu____2774  in
                   uu____2768 :: uu____2770  in
                 uu____2764 :: uu____2765  in
               (if for_free then "_for_free " else "") :: uu____2761  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2758)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2850 =
      let uu____2851 = FStar_Options.ugly ()  in Prims.op_Negation uu____2851
       in
    if uu____2850
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2857 -> ""
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
             (lid,univs1,tps,k,uu____2868,uu____2869) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2881 = FStar_Options.print_universes ()  in
             if uu____2881
             then
               let uu____2882 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2882 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2887,uu____2888,uu____2889) ->
             let uu____2894 = FStar_Options.print_universes ()  in
             if uu____2894
             then
               let uu____2895 = univ_names_to_string univs1  in
               let uu____2896 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2895
                 lid.FStar_Ident.str uu____2896
             else
               (let uu____2898 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2898)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2902 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2903 =
               let uu____2904 = FStar_Options.print_universes ()  in
               if uu____2904
               then
                 let uu____2905 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2905
               else ""  in
             let uu____2907 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2902
               lid.FStar_Ident.str uu____2903 uu____2907
         | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
             let uu____2911 = FStar_Options.print_universes ()  in
             if uu____2911
             then
               let uu____2912 = univ_names_to_string us  in
               let uu____2913 = term_to_string f  in
               FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
                 uu____2912 uu____2913
             else
               (let uu____2915 = term_to_string f  in
                FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str
                  uu____2915)
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2917) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2923 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2923
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2925) ->
             let uu____2934 =
               let uu____2935 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2935 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2934
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2971) -> lift_wp
               | (uu____2978,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2986 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2986 with
              | (us,t) ->
                  let uu____2997 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2998 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2999 = univ_names_to_string us  in
                  let uu____3000 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2997 uu____2998 uu____2999 uu____3000)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____3010 = FStar_Options.print_universes ()  in
             if uu____3010
             then
               let uu____3011 =
                 let uu____3016 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____3016  in
               (match uu____3011 with
                | (univs2,t) ->
                    let uu____3029 =
                      let uu____3034 =
                        let uu____3035 = FStar_Syntax_Subst.compress t  in
                        uu____3035.FStar_Syntax_Syntax.n  in
                      match uu____3034 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____3064 -> failwith "impossible"  in
                    (match uu____3029 with
                     | (tps1,c1) ->
                         let uu____3071 = sli l  in
                         let uu____3072 = univ_names_to_string univs2  in
                         let uu____3073 = binders_to_string " " tps1  in
                         let uu____3074 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____3071 uu____3072 uu____3073 uu____3074))
             else
               (let uu____3076 = sli l  in
                let uu____3077 = binders_to_string " " tps  in
                let uu____3078 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____3076 uu____3077
                  uu____3078)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____3085 =
               let uu____3086 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____3086  in
             let uu____3091 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____3085 uu____3091
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____3092 ->
           let uu____3095 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____3095 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3106 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3106 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3112,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3114;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3116;
                       FStar_Syntax_Syntax.lbdef = uu____3117;
                       FStar_Syntax_Syntax.lbattrs = uu____3118;
                       FStar_Syntax_Syntax.lbpos = uu____3119;_}::[]),uu____3120)
        ->
        let uu____3141 = lbname_to_string lb  in
        let uu____3142 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3141 uu____3142
    | uu____3143 ->
        let uu____3144 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3144 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3160 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3161 =
      let uu____3162 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3162 (FStar_String.concat "\n")  in
    let uu____3167 =
      let uu____3168 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3168 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3160 uu____3161 uu____3167
  
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
          (let uu____3202 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3202))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3209 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3209)));
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
           (let uu____3243 = f x  in
            FStar_Util.string_builder_append strb uu____3243);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3250 = f x1  in
                 FStar_Util.string_builder_append strb uu____3250)) xs;
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
           (let uu____3288 = f x  in
            FStar_Util.string_builder_append strb uu____3288);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3295 = f x1  in
                 FStar_Util.string_builder_append strb uu____3295)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3311 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3311
  