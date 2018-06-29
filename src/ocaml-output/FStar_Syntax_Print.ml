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
               thunk;
             FStar_Syntax_Syntax.ltyp = uu____1331;
             FStar_Syntax_Syntax.rng = uu____1332;_}
           ->
           let uu____1339 = FStar_Common.force_thunk thunk  in
           term_to_string uu____1339
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1383 =
             let uu____1384 =
               let uu____1393 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1393  in
             uu____1384 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1383
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1448;_})
           ->
           let uu____1463 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1463
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1465;_})
           ->
           let uu____1480 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1480
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1500 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1534 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1556  ->
                                 match uu____1556 with
                                 | (t1,uu____1564) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1534
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1500 (FStar_String.concat "\\/")  in
           let uu____1573 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1573
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1585 = tag_of_term t  in
           let uu____1586 = sli m  in
           let uu____1587 = term_to_string t'  in
           let uu____1588 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1585 uu____1586
             uu____1587 uu____1588
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1601 = tag_of_term t  in
           let uu____1602 = term_to_string t'  in
           let uu____1603 = sli m0  in
           let uu____1604 = sli m1  in
           let uu____1605 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1601
             uu____1602 uu____1603 uu____1604 uu____1605
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1614 = FStar_Range.string_of_range r  in
           let uu____1615 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1614
             uu____1615
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1622 = lid_to_string l  in
           let uu____1623 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1624 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1622 uu____1623
             uu____1624
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1626) ->
           let uu____1631 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1631
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1633 = db_to_string x3  in
           let uu____1634 =
             let uu____1635 =
               let uu____1636 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1636 ")"  in
             Prims.strcat ":(" uu____1635  in
           Prims.strcat uu____1633 uu____1634
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1640)) ->
           let uu____1655 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1655
           then ctx_uvar_to_string u
           else
             (let uu____1657 =
                let uu____1658 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1658  in
              Prims.strcat "?" uu____1657)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1677 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1677
           then
             let uu____1678 = ctx_uvar_to_string u  in
             let uu____1679 =
               let uu____1680 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1680 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1678 uu____1679
           else
             (let uu____1692 =
                let uu____1693 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1693  in
              Prims.strcat "?" uu____1692)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1696 = FStar_Options.print_universes ()  in
           if uu____1696
           then
             let uu____1697 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1697
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1721 = binders_to_string " -> " bs  in
           let uu____1722 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1721 uu____1722
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1751 = binders_to_string " " bs  in
                let uu____1752 = term_to_string t2  in
                let uu____1753 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1757 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1757)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1751 uu____1752
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1753
            | uu____1760 ->
                let uu____1763 = binders_to_string " " bs  in
                let uu____1764 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1763 uu____1764)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1771 = bv_to_string xt  in
           let uu____1772 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1773 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1771 uu____1772 uu____1773
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1802 = term_to_string t  in
           let uu____1803 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1802 uu____1803
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1822 = lbs_to_string [] lbs  in
           let uu____1823 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1822 uu____1823
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1884 =
                   let uu____1885 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1885
                     (FStar_Util.dflt "default")
                    in
                 let uu____1890 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1884 uu____1890
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1906 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1906
              in
           let uu____1907 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1907 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1946 = term_to_string head1  in
           let uu____1947 =
             let uu____1948 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1978  ->
                       match uu____1978 with
                       | (p,wopt,e) ->
                           let uu____1994 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1995 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1997 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1997
                              in
                           let uu____1998 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1994
                             uu____1995 uu____1998))
                in
             FStar_Util.concat_l "\n\t|" uu____1948  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1946 uu____1947
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2005 = FStar_Options.print_universes ()  in
           if uu____2005
           then
             let uu____2006 = term_to_string t  in
             let uu____2007 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2006 uu____2007
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2010 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2011 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2012 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2010 uu____2011
      uu____2012

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___206_2013  ->
    match uu___206_2013 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2016 = FStar_Util.string_of_int i  in
        let uu____2017 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2016 uu____2017
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2020 = bv_to_string x  in
        let uu____2021 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2020 uu____2021
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2028 = bv_to_string x  in
        let uu____2029 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2028 uu____2029
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2032 = FStar_Util.string_of_int i  in
        let uu____2033 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2032 uu____2033
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2036 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2036

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2038 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2038 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2048 =
      let uu____2049 = FStar_Options.ugly ()  in Prims.op_Negation uu____2049
       in
    if uu____2048
    then
      let e =
        let uu____2051 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2051  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2074 = fv_to_string l  in
           let uu____2075 =
             let uu____2076 =
               FStar_List.map
                 (fun uu____2087  ->
                    match uu____2087 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2076 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2074 uu____2075
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2099) ->
           let uu____2104 = FStar_Options.print_bound_var_types ()  in
           if uu____2104
           then
             let uu____2105 = bv_to_string x1  in
             let uu____2106 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2105 uu____2106
           else
             (let uu____2108 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2108)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2110 = FStar_Options.print_bound_var_types ()  in
           if uu____2110
           then
             let uu____2111 = bv_to_string x1  in
             let uu____2112 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2111 uu____2112
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2116 = FStar_Options.print_real_names ()  in
           if uu____2116
           then
             let uu____2117 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____2117
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2129 = quals_to_string' quals  in
      let uu____2130 =
        let uu____2131 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2147 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2148 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2149 =
                    let uu____2150 = FStar_Options.print_universes ()  in
                    if uu____2150
                    then
                      let uu____2151 =
                        let uu____2152 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2152 ">"  in
                      Prims.strcat "<" uu____2151
                    else ""  in
                  let uu____2154 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2155 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2147
                    uu____2148 uu____2149 uu____2154 uu____2155))
           in
        FStar_Util.concat_l "\n and " uu____2131  in
      FStar_Util.format3 "%slet %s %s" uu____2129
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2130

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___207_2159  ->
    match uu___207_2159 with
    | [] -> ""
    | tms ->
        let uu____2165 =
          let uu____2166 =
            FStar_List.map
              (fun t  ->
                 let uu____2172 = term_to_string t  in paren uu____2172) tms
             in
          FStar_All.pipe_right uu____2166 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2165

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2176 = FStar_Options.print_effect_args ()  in
    if uu____2176
    then
      let uu____2177 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2177
    else
      (let uu____2179 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2180 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2179 uu____2180)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___208_2181  ->
    match uu___208_2181 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2182 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2185 = aqual_to_string aq  in Prims.strcat uu____2185 s

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2194 =
        let uu____2195 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2195  in
      if uu____2194
      then
        let uu____2196 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2196 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2202 = b  in
         match uu____2202 with
         | (a,imp) ->
             let uu____2215 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2215
             then
               let uu____2216 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2216
             else
               (let uu____2218 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2220 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2220)
                   in
                if uu____2218
                then
                  let uu____2221 = nm_to_string a  in
                  imp_to_string uu____2221 imp
                else
                  (let uu____2223 =
                     let uu____2224 = nm_to_string a  in
                     let uu____2225 =
                       let uu____2226 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2226  in
                     Prims.strcat uu____2224 uu____2225  in
                   imp_to_string uu____2223 imp)))

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
        let uu____2240 = FStar_Options.print_implicits ()  in
        if uu____2240 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2244 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2244 (FStar_String.concat sep)
      else
        (let uu____2266 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2266 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___209_2275  ->
    match uu___209_2275 with
    | (a,imp) ->
        let uu____2282 = term_to_string a  in imp_to_string uu____2282 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2291 = FStar_Options.print_implicits ()  in
      if uu____2291 then args else filter_imp args  in
    let uu____2301 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2301 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2320 = FStar_Options.ugly ()  in
      if uu____2320
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2325 =
      let uu____2326 = FStar_Options.ugly ()  in Prims.op_Negation uu____2326
       in
    if uu____2325
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2340 =
             let uu____2341 = FStar_Syntax_Subst.compress t  in
             uu____2341.FStar_Syntax_Syntax.n  in
           (match uu____2340 with
            | FStar_Syntax_Syntax.Tm_type uu____2344 when
                let uu____2345 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2345 -> term_to_string t
            | uu____2346 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2348 = univ_to_string u  in
                     let uu____2349 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2348 uu____2349
                 | uu____2350 ->
                     let uu____2353 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2353))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2364 =
             let uu____2365 = FStar_Syntax_Subst.compress t  in
             uu____2365.FStar_Syntax_Syntax.n  in
           (match uu____2364 with
            | FStar_Syntax_Syntax.Tm_type uu____2368 when
                let uu____2369 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2369 -> term_to_string t
            | uu____2370 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2372 = univ_to_string u  in
                     let uu____2373 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2372 uu____2373
                 | uu____2374 ->
                     let uu____2377 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2377))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2380 = FStar_Options.print_effect_args ()  in
             if uu____2380
             then
               let uu____2381 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2382 =
                 let uu____2383 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2383 (FStar_String.concat ", ")
                  in
               let uu____2392 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2393 =
                 let uu____2394 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2394 (FStar_String.concat ", ")
                  in
               let uu____2411 =
                 let uu____2412 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2412 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2381
                 uu____2382 uu____2392 uu____2393 uu____2411
             else
               (let uu____2422 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___210_2426  ->
                           match uu___210_2426 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2427 -> false)))
                    &&
                    (let uu____2429 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2429)
                   in
                if uu____2422
                then
                  let uu____2430 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2430
                else
                  (let uu____2432 =
                     ((let uu____2435 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2435) &&
                        (let uu____2437 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2437))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2432
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2439 =
                        (let uu____2442 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2442) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___211_2446  ->
                                   match uu___211_2446 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2447 -> false)))
                         in
                      if uu____2439
                      then
                        let uu____2448 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2448
                      else
                        (let uu____2450 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2451 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2450 uu____2451))))
              in
           let dec =
             let uu____2453 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___212_2463  ->
                       match uu___212_2463 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2469 =
                             let uu____2470 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2470
                              in
                           [uu____2469]
                       | uu____2471 -> []))
                in
             FStar_All.pipe_right uu____2453 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2475 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___213_2481  ->
    match uu___213_2481 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2496 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2530 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2552  ->
                              match uu____2552 with
                              | (t,uu____2560) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2530
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2496 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2570 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2570
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2573) ->
        let uu____2574 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2574
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2582 = sli m  in
        let uu____2583 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2582 uu____2583
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2591 = sli m  in
        let uu____2592 = sli m'  in
        let uu____2593 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2591
          uu____2592 uu____2593

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2604 = FStar_Options.ugly ()  in
      if uu____2604
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
      let uu____2618 = b  in
      match uu____2618 with
      | (a,imp) ->
          let n1 =
            let uu____2626 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2626
            then FStar_Util.JsonNull
            else
              (let uu____2628 =
                 let uu____2629 = nm_to_string a  in
                 imp_to_string uu____2629 imp  in
               FStar_Util.JsonStr uu____2628)
             in
          let t =
            let uu____2631 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2631  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2654 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2654
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2668 = FStar_Options.print_universes ()  in
    if uu____2668 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2675 =
      let uu____2676 = FStar_Options.ugly ()  in Prims.op_Negation uu____2676
       in
    if uu____2675
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2680 = s  in
       match uu____2680 with
       | (us,t) ->
           let uu____2691 =
             let uu____2692 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2692  in
           let uu____2693 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2691 uu____2693)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2699 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2700 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2701 =
      let uu____2702 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2702  in
    let uu____2703 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2704 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2699 uu____2700 uu____2701
      uu____2703 uu____2704
  
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
          let uu____2729 =
            let uu____2730 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2730  in
          if uu____2729
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2744 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2744 (FStar_String.concat ",\n\t")
                in
             let uu____2753 =
               let uu____2756 =
                 let uu____2759 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2760 =
                   let uu____2763 =
                     let uu____2764 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2764  in
                   let uu____2765 =
                     let uu____2768 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2769 =
                       let uu____2772 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2773 =
                         let uu____2776 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2777 =
                           let uu____2780 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2781 =
                             let uu____2784 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2785 =
                               let uu____2788 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2789 =
                                 let uu____2792 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2793 =
                                   let uu____2796 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2797 =
                                     let uu____2800 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2801 =
                                       let uu____2804 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2805 =
                                         let uu____2808 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2809 =
                                           let uu____2812 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2813 =
                                             let uu____2816 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2817 =
                                               let uu____2820 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2821 =
                                                 let uu____2824 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2825 =
                                                   let uu____2828 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2828]  in
                                                 uu____2824 :: uu____2825  in
                                               uu____2820 :: uu____2821  in
                                             uu____2816 :: uu____2817  in
                                           uu____2812 :: uu____2813  in
                                         uu____2808 :: uu____2809  in
                                       uu____2804 :: uu____2805  in
                                     uu____2800 :: uu____2801  in
                                   uu____2796 :: uu____2797  in
                                 uu____2792 :: uu____2793  in
                               uu____2788 :: uu____2789  in
                             uu____2784 :: uu____2785  in
                           uu____2780 :: uu____2781  in
                         uu____2776 :: uu____2777  in
                       uu____2772 :: uu____2773  in
                     uu____2768 :: uu____2769  in
                   uu____2763 :: uu____2765  in
                 uu____2759 :: uu____2760  in
               (if for_free then "_for_free " else "") :: uu____2756  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2753)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2845 =
      let uu____2846 = FStar_Options.ugly ()  in Prims.op_Negation uu____2846
       in
    if uu____2845
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2852 -> ""
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
             (lid,univs1,tps,k,uu____2863,uu____2864) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2876 = FStar_Options.print_universes ()  in
             if uu____2876
             then
               let uu____2877 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2877 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2882,uu____2883,uu____2884) ->
             let uu____2889 = FStar_Options.print_universes ()  in
             if uu____2889
             then
               let uu____2890 = univ_names_to_string univs1  in
               let uu____2891 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2890
                 lid.FStar_Ident.str uu____2891
             else
               (let uu____2893 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2893)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2897 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2898 =
               let uu____2899 = FStar_Options.print_universes ()  in
               if uu____2899
               then
                 let uu____2900 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2900
               else ""  in
             let uu____2902 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2897
               lid.FStar_Ident.str uu____2898 uu____2902
         | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
             let uu____2906 = FStar_Options.print_universes ()  in
             if uu____2906
             then
               let uu____2907 = univ_names_to_string us  in
               let uu____2908 = term_to_string f  in
               FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
                 uu____2907 uu____2908
             else
               (let uu____2910 = term_to_string f  in
                FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str
                  uu____2910)
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2912) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2918 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2918
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2920) ->
             let uu____2929 =
               let uu____2930 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2930 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2929
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2966) -> lift_wp
               | (uu____2973,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2981 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2981 with
              | (us,t) ->
                  let uu____2992 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2993 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2994 = univ_names_to_string us  in
                  let uu____2995 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2992 uu____2993 uu____2994 uu____2995)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____3005 = FStar_Options.print_universes ()  in
             if uu____3005
             then
               let uu____3006 =
                 let uu____3011 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____3011  in
               (match uu____3006 with
                | (univs2,t) ->
                    let uu____3024 =
                      let uu____3029 =
                        let uu____3030 = FStar_Syntax_Subst.compress t  in
                        uu____3030.FStar_Syntax_Syntax.n  in
                      match uu____3029 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____3059 -> failwith "impossible"  in
                    (match uu____3024 with
                     | (tps1,c1) ->
                         let uu____3066 = sli l  in
                         let uu____3067 = univ_names_to_string univs2  in
                         let uu____3068 = binders_to_string " " tps1  in
                         let uu____3069 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____3066 uu____3067 uu____3068 uu____3069))
             else
               (let uu____3071 = sli l  in
                let uu____3072 = binders_to_string " " tps  in
                let uu____3073 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____3071 uu____3072
                  uu____3073)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____3080 =
               let uu____3081 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____3081  in
             let uu____3086 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____3080 uu____3086
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____3087 ->
           let uu____3090 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____3090 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3101 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3101 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3107,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3109;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3111;
                       FStar_Syntax_Syntax.lbdef = uu____3112;
                       FStar_Syntax_Syntax.lbattrs = uu____3113;
                       FStar_Syntax_Syntax.lbpos = uu____3114;_}::[]),uu____3115)
        ->
        let uu____3136 = lbname_to_string lb  in
        let uu____3137 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3136 uu____3137
    | uu____3138 ->
        let uu____3139 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3139 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3155 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3156 =
      let uu____3157 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3157 (FStar_String.concat "\n")  in
    let uu____3162 =
      let uu____3163 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3163 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____3155 uu____3156 uu____3162
  
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
          (let uu____3197 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3197))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3204 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3204)));
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
           (let uu____3238 = f x  in
            FStar_Util.string_builder_append strb uu____3238);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3245 = f x1  in
                 FStar_Util.string_builder_append strb uu____3245)) xs;
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
           (let uu____3283 = f x  in
            FStar_Util.string_builder_append strb uu____3283);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3290 = f x1  in
                 FStar_Util.string_builder_append strb uu____3290)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3306 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3306
  