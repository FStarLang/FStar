open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_56152  ->
    match uu___429_56152 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____56156 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____56156
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____56161 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____56161
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____56165 =
          let uu____56167 = delta_depth_to_string d  in
          Prims.op_Hat uu____56167 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____56165
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____56179 = FStar_Options.print_real_names ()  in
    if uu____56179
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56206 =
      let uu____56208 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____56208  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56206
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56218 = FStar_Options.print_real_names ()  in
    if uu____56218
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56231 =
      let uu____56233 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____56233  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56231
  
let (infix_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list) =
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
let (unary_prim_ops : (FStar_Ident.lident * Prims.string) Prims.list) =
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
      | uu____56455 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____56468 -> failwith "get_lid"
  
let (is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
  
let (is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
  
let (quants : (FStar_Ident.lident * Prims.string) Prims.list) =
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
  'Auu____56571 'Auu____56572 .
    ('Auu____56571,'Auu____56572) FStar_Util.either -> Prims.bool
  =
  fun uu___430_56582  ->
    match uu___430_56582 with
    | FStar_Util.Inl uu____56587 -> false
    | FStar_Util.Inr uu____56589 -> true
  
let filter_imp :
  'Auu____56596 .
    ('Auu____56596 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____56596 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_56651  ->
            match uu___431_56651 with
            | (uu____56659,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____56666,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____56667)) -> false
            | (uu____56672,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____56673)) -> false
            | uu____56679 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____56697 =
      let uu____56698 = FStar_Syntax_Subst.compress e  in
      uu____56698.FStar_Syntax_Syntax.n  in
    match uu____56697 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____56759 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____56759
        then
          let uu____56768 =
            let uu____56773 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____56773  in
          (match uu____56768 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____56784 =
                 let uu____56787 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____56787 :: xs  in
               FStar_Pervasives_Native.Some uu____56784
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____56799 ->
        let uu____56800 = is_lex_top e  in
        if uu____56800
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____56848 = f hd1  in if uu____56848 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____56880 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____56880
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56911 = get_lid e  in find_lid uu____56911 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56923 = get_lid e  in find_lid uu____56923 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____56935 = get_lid t  in find_lid uu____56935 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_56949  ->
    match uu___432_56949 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____56960 = FStar_Options.hide_uvar_nums ()  in
    if uu____56960
    then "?"
    else
      (let uu____56967 =
         let uu____56969 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____56969 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____56967)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____56981 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____56983 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____56981 uu____56983
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____57009 = FStar_Options.hide_uvar_nums ()  in
    if uu____57009
    then "?"
    else
      (let uu____57016 =
         let uu____57018 =
           let uu____57020 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____57020 FStar_Util.string_of_int  in
         let uu____57024 =
           let uu____57026 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____57026  in
         Prims.op_Hat uu____57018 uu____57024  in
       Prims.op_Hat "?" uu____57016)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____57054 = FStar_Syntax_Subst.compress_univ u  in
      match uu____57054 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____57067 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____57078 = FStar_Syntax_Subst.compress_univ u  in
    match uu____57078 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____57089 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____57089
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____57096 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____57096
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____57101 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____57101 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____57122 = univ_to_string u2  in
             let uu____57124 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____57122 uu____57124)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____57130 =
          let uu____57132 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____57132 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____57130
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____57151 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____57151 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____57168 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____57168 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_57186  ->
    match uu___433_57186 with
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
        let uu____57202 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____57202
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____57207 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____57207
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____57220 =
          let uu____57222 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57222  in
        let uu____57223 =
          let uu____57225 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57225 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____57220 uu____57223
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____57251 =
          let uu____57253 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57253  in
        let uu____57254 =
          let uu____57256 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57256 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____57251
          uu____57254
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____57273 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____57273
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
    | uu____57296 ->
        let uu____57299 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____57299 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____57327 ->
        let uu____57330 = quals_to_string quals  in
        Prims.op_Hat uu____57330 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____57526 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____57526
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____57530 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____57530
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____57534 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____57534
    | FStar_Syntax_Syntax.Tm_uinst uu____57537 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____57545 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____57547 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57549,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____57550;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57564,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____57565;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____57579 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____57599 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____57615 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____57623 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____57641 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____57665 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____57693 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____57708 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____57722,m) ->
        let uu____57760 = FStar_ST.op_Bang m  in
        (match uu____57760 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____57818 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____57824,m) ->
        let uu____57830 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____57830
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____57834 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____57837 =
      let uu____57839 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____57839  in
    if uu____57837
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____57853 = FStar_Options.print_implicits ()  in
         if uu____57853 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____57861 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____57886,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____57912,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____57914;
             FStar_Syntax_Syntax.rng = uu____57915;_}
           ->
           let uu____57926 =
             let uu____57928 =
               let uu____57930 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____57930  in
             Prims.op_Hat uu____57928 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____57926
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____57976 =
             let uu____57978 =
               let uu____57980 =
                 let uu____57981 =
                   let uu____57990 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____57990  in
                 uu____57981 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____57980  in
             Prims.op_Hat uu____57978 "]"  in
           Prims.op_Hat "[lazy:" uu____57976
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____58059 =
                  match uu____58059 with
                  | (bv,t) ->
                      let uu____58067 = bv_to_string bv  in
                      let uu____58069 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____58067 uu____58069
                   in
                let uu____58072 = term_to_string tm  in
                let uu____58074 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____58072 uu____58074
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____58083 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____58083)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____58106 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____58143 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____58168  ->
                                 match uu____58168 with
                                 | (t1,uu____58177) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____58143
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____58106 (FStar_String.concat "\\/")  in
           let uu____58192 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____58192
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____58206 = tag_of_term t  in
           let uu____58208 = sli m  in
           let uu____58210 = term_to_string t'  in
           let uu____58212 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____58206
             uu____58208 uu____58210 uu____58212
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____58227 = tag_of_term t  in
           let uu____58229 = term_to_string t'  in
           let uu____58231 = sli m0  in
           let uu____58233 = sli m1  in
           let uu____58235 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____58227 uu____58229 uu____58231 uu____58233 uu____58235
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____58250 = FStar_Range.string_of_range r  in
           let uu____58252 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____58250
             uu____58252
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____58261 = lid_to_string l  in
           let uu____58263 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____58265 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____58261
             uu____58263 uu____58265
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____58269) ->
           let uu____58274 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____58274
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____58278 = db_to_string x3  in
           let uu____58280 =
             let uu____58282 =
               let uu____58284 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____58284 ")"  in
             Prims.op_Hat ":(" uu____58282  in
           Prims.op_Hat uu____58278 uu____58280
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____58291)) ->
           let uu____58306 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58306
           then ctx_uvar_to_string u
           else
             (let uu____58312 =
                let uu____58314 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58314  in
              Prims.op_Hat "?" uu____58312)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____58337 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58337
           then
             let uu____58341 = ctx_uvar_to_string u  in
             let uu____58343 =
               let uu____58345 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____58345 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____58341 uu____58343
           else
             (let uu____58364 =
                let uu____58366 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58366  in
              Prims.op_Hat "?" uu____58364)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____58373 = FStar_Options.print_universes ()  in
           if uu____58373
           then
             let uu____58377 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____58377
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____58405 = binders_to_string " -> " bs  in
           let uu____58408 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____58405 uu____58408
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____58440 = binders_to_string " " bs  in
                let uu____58443 = term_to_string t2  in
                let uu____58445 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____58454 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____58454)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____58440 uu____58443
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____58445
            | uu____58458 ->
                let uu____58461 = binders_to_string " " bs  in
                let uu____58464 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____58461 uu____58464)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____58473 = bv_to_string xt  in
           let uu____58475 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____58478 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____58473 uu____58475
             uu____58478
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____58510 = term_to_string t  in
           let uu____58512 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____58510 uu____58512
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____58535 = lbs_to_string [] lbs  in
           let uu____58537 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____58535 uu____58537
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____58602 =
                   let uu____58604 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____58604
                     (FStar_Util.dflt "default")
                    in
                 let uu____58615 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____58602 uu____58615
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____58636 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____58636
              in
           let uu____58639 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____58639 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____58680 = term_to_string head1  in
           let uu____58682 =
             let uu____58684 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____58717  ->
                       match uu____58717 with
                       | (p,wopt,e) ->
                           let uu____58734 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____58737 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____58742 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____58742
                              in
                           let uu____58746 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____58734
                             uu____58737 uu____58746))
                in
             FStar_Util.concat_l "\n\t|" uu____58684  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____58680
             uu____58682
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____58758 = FStar_Options.print_universes ()  in
           if uu____58758
           then
             let uu____58762 = term_to_string t  in
             let uu____58764 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____58762 uu____58764
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____58771 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____58774 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____58776 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____58771 uu____58774
      uu____58776

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_58779  ->
    match uu___434_58779 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____58785 = FStar_Util.string_of_int i  in
        let uu____58787 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____58785 uu____58787
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____58794 = bv_to_string x  in
        let uu____58796 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____58794 uu____58796
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____58805 = bv_to_string x  in
        let uu____58807 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____58805 uu____58807
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____58814 = FStar_Util.string_of_int i  in
        let uu____58816 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____58814 uu____58816
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____58823 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____58823

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____58827 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____58827 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____58843 =
      let uu____58845 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____58845  in
    if uu____58843
    then
      let e =
        let uu____58850 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____58850  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____58879 = fv_to_string l  in
           let uu____58881 =
             let uu____58883 =
               FStar_List.map
                 (fun uu____58897  ->
                    match uu____58897 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____58883 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____58879 uu____58881
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____58922) ->
           let uu____58927 = FStar_Options.print_bound_var_types ()  in
           if uu____58927
           then
             let uu____58931 = bv_to_string x1  in
             let uu____58933 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____58931 uu____58933
           else
             (let uu____58938 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____58938)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____58942 = FStar_Options.print_bound_var_types ()  in
           if uu____58942
           then
             let uu____58946 = bv_to_string x1  in
             let uu____58948 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____58946 uu____58948
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____58955 = FStar_Options.print_bound_var_types ()  in
           if uu____58955
           then
             let uu____58959 = bv_to_string x1  in
             let uu____58961 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____58959 uu____58961
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____58970 = quals_to_string' quals  in
      let uu____58972 =
        let uu____58974 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____58994 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____58996 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____58998 =
                    let uu____59000 = FStar_Options.print_universes ()  in
                    if uu____59000
                    then
                      let uu____59004 =
                        let uu____59006 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____59006 ">"  in
                      Prims.op_Hat "<" uu____59004
                    else ""  in
                  let uu____59013 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____59015 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____58994
                    uu____58996 uu____58998 uu____59013 uu____59015))
           in
        FStar_Util.concat_l "\n and " uu____58974  in
      FStar_Util.format3 "%slet %s %s" uu____58970
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____58972

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_59030  ->
    match uu___435_59030 with
    | [] -> ""
    | tms ->
        let uu____59038 =
          let uu____59040 =
            FStar_List.map
              (fun t  ->
                 let uu____59048 = term_to_string t  in paren uu____59048)
              tms
             in
          FStar_All.pipe_right uu____59040 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____59038

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____59057 = FStar_Options.print_effect_args ()  in
    if uu____59057
    then
      let uu____59061 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____59061
    else
      (let uu____59064 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____59066 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____59064 uu____59066)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_59070  ->
      match uu___436_59070 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.op_Hat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.op_Hat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.op_Hat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.op_Hat "[|" (Prims.op_Hat s "|]")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____59088 =
            let uu____59090 = term_to_string t  in
            Prims.op_Hat uu____59090 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____59088
      | FStar_Pervasives_Native.None  -> s

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq  -> aqual_to_string' "" aq

and (imp_to_string :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  = fun s  -> fun aq  -> aqual_to_string' s aq

and (binder_to_string' :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____59110 =
        let uu____59112 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____59112  in
      if uu____59110
      then
        let uu____59116 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____59116 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____59127 = b  in
         match uu____59127 with
         | (a,imp) ->
             let uu____59141 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____59141
             then
               let uu____59145 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____59145
             else
               (let uu____59150 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____59153 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____59153)
                   in
                if uu____59150
                then
                  let uu____59157 = nm_to_string a  in
                  imp_to_string uu____59157 imp
                else
                  (let uu____59161 =
                     let uu____59163 = nm_to_string a  in
                     let uu____59165 =
                       let uu____59167 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____59167  in
                     Prims.op_Hat uu____59163 uu____59165  in
                   imp_to_string uu____59161 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  = fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____59186 = FStar_Options.print_implicits ()  in
        if uu____59186 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____59197 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____59197 (FStar_String.concat sep)
      else
        (let uu____59225 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____59225 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_59239  ->
    match uu___437_59239 with
    | (a,imp) ->
        let uu____59253 = term_to_string a  in imp_to_string uu____59253 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____59265 = FStar_Options.print_implicits ()  in
      if uu____59265 then args else filter_imp args  in
    let uu____59280 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59280 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____59309 = FStar_Options.ugly ()  in
      if uu____59309
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____59320 =
      let uu____59322 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59322  in
    if uu____59320
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____59343 =
             let uu____59344 = FStar_Syntax_Subst.compress t  in
             uu____59344.FStar_Syntax_Syntax.n  in
           (match uu____59343 with
            | FStar_Syntax_Syntax.Tm_type uu____59348 when
                let uu____59349 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59349 -> term_to_string t
            | uu____59351 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59354 = univ_to_string u  in
                     let uu____59356 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____59354 uu____59356
                 | uu____59359 ->
                     let uu____59362 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____59362))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____59375 =
             let uu____59376 = FStar_Syntax_Subst.compress t  in
             uu____59376.FStar_Syntax_Syntax.n  in
           (match uu____59375 with
            | FStar_Syntax_Syntax.Tm_type uu____59380 when
                let uu____59381 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59381 -> term_to_string t
            | uu____59383 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59386 = univ_to_string u  in
                     let uu____59388 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____59386 uu____59388
                 | uu____59391 ->
                     let uu____59394 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____59394))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____59400 = FStar_Options.print_effect_args ()  in
             if uu____59400
             then
               let uu____59404 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____59406 =
                 let uu____59408 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____59408 (FStar_String.concat ", ")
                  in
               let uu____59423 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____59425 =
                 let uu____59427 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____59427 (FStar_String.concat ", ")
                  in
               let uu____59454 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____59404 uu____59406 uu____59423 uu____59425 uu____59454
             else
               (let uu____59459 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_59465  ->
                           match uu___438_59465 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____59468 -> false)))
                    &&
                    (let uu____59471 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____59471)
                   in
                if uu____59459
                then
                  let uu____59475 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____59475
                else
                  (let uu____59480 =
                     ((let uu____59484 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____59484) &&
                        (let uu____59487 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____59487))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____59480
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____59493 =
                        (let uu____59497 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____59497) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_59503  ->
                                   match uu___439_59503 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____59506 -> false)))
                         in
                      if uu____59493
                      then
                        let uu____59510 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____59510
                      else
                        (let uu____59515 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____59517 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____59515 uu____59517))))
              in
           let dec =
             let uu____59522 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_59535  ->
                       match uu___440_59535 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____59542 =
                             let uu____59544 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____59544
                              in
                           [uu____59542]
                       | uu____59549 -> []))
                in
             FStar_All.pipe_right uu____59522 (FStar_String.concat " ")  in
           FStar_Util.format2 "%s%s" basic dec)

and (cflag_to_string : FStar_Syntax_Syntax.cflag -> Prims.string) =
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
    | FStar_Syntax_Syntax.DECREASES uu____59568 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_59578  ->
    match uu___441_59578 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____59595 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____59632 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____59657  ->
                              match uu____59657 with
                              | (t,uu____59666) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____59632
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____59595 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____59683 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____59683
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____59688) ->
        let uu____59693 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____59693
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____59704 = sli m  in
        let uu____59706 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____59704 uu____59706
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____59716 = sli m  in
        let uu____59718 = sli m'  in
        let uu____59720 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____59716
          uu____59718 uu____59720

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____59735 = FStar_Options.ugly ()  in
      if uu____59735
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
      let uu____59756 = b  in
      match uu____59756 with
      | (a,imp) ->
          let n1 =
            let uu____59764 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____59764
            then FStar_Util.JsonNull
            else
              (let uu____59769 =
                 let uu____59771 = nm_to_string a  in
                 imp_to_string uu____59771 imp  in
               FStar_Util.JsonStr uu____59769)
             in
          let t =
            let uu____59774 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____59774  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____59806 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____59806
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____59824 = FStar_Options.print_universes ()  in
    if uu____59824 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____59840 =
      let uu____59842 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59842  in
    if uu____59840
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____59852 = s  in
       match uu____59852 with
       | (us,t) ->
           let uu____59864 =
             let uu____59866 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____59866  in
           let uu____59870 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____59864 uu____59870)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____59880 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____59882 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____59885 =
      let uu____59887 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____59887  in
    let uu____59891 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____59893 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____59880 uu____59882
      uu____59885 uu____59891 uu____59893
  
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
          let uu____59924 =
            let uu____59926 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____59926  in
          if uu____59924
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____59947 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____59947 (FStar_String.concat ",\n\t")
                in
             let uu____59962 =
               let uu____59966 =
                 let uu____59970 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____59972 =
                   let uu____59976 =
                     let uu____59978 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____59978  in
                   let uu____59982 =
                     let uu____59986 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____59989 =
                       let uu____59993 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____59995 =
                         let uu____59999 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____60001 =
                           let uu____60005 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____60007 =
                             let uu____60011 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____60013 =
                               let uu____60017 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____60019 =
                                 let uu____60023 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____60025 =
                                   let uu____60029 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____60031 =
                                     let uu____60035 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____60037 =
                                       let uu____60041 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____60043 =
                                         let uu____60047 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____60049 =
                                           let uu____60053 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____60055 =
                                             let uu____60059 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____60061 =
                                               let uu____60065 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____60067 =
                                                 let uu____60071 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____60073 =
                                                   let uu____60077 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____60077]  in
                                                 uu____60071 :: uu____60073
                                                  in
                                               uu____60065 :: uu____60067  in
                                             uu____60059 :: uu____60061  in
                                           uu____60053 :: uu____60055  in
                                         uu____60047 :: uu____60049  in
                                       uu____60041 :: uu____60043  in
                                     uu____60035 :: uu____60037  in
                                   uu____60029 :: uu____60031  in
                                 uu____60023 :: uu____60025  in
                               uu____60017 :: uu____60019  in
                             uu____60011 :: uu____60013  in
                           uu____60005 :: uu____60007  in
                         uu____59999 :: uu____60001  in
                       uu____59993 :: uu____59995  in
                     uu____59986 :: uu____59989  in
                   uu____59976 :: uu____59982  in
                 uu____59970 :: uu____59972  in
               (if for_free then "_for_free " else "") :: uu____59966  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____59962)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let basic =
      match x.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
          "#light \"off\""
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          (FStar_Pervasives_Native.None )) -> "#reset-options"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
          (FStar_Pervasives_Native.Some s)) ->
          FStar_Util.format1 "#reset-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
          FStar_Util.format1 "#set-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.None )) -> "#push-options"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PushOptions
          (FStar_Pervasives_Native.Some s)) ->
          FStar_Util.format1 "#push-options \"%s\"" s
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
          "#pop-options"
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univs1,tps,k,uu____60151,uu____60152) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____60168 = FStar_Options.print_universes ()  in
          if uu____60168
          then
            let uu____60172 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____60172 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____60181,uu____60182,uu____60183) ->
          let uu____60190 = FStar_Options.print_universes ()  in
          if uu____60190
          then
            let uu____60194 = univ_names_to_string univs1  in
            let uu____60196 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____60194
              lid.FStar_Ident.str uu____60196
          else
            (let uu____60201 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____60201)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____60207 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____60209 =
            let uu____60211 = FStar_Options.print_universes ()  in
            if uu____60211
            then
              let uu____60215 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____60215
            else ""  in
          let uu____60221 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____60207
            lid.FStar_Ident.str uu____60209 uu____60221
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____60227 = FStar_Options.print_universes ()  in
          if uu____60227
          then
            let uu____60231 = univ_names_to_string us  in
            let uu____60233 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____60231 uu____60233
          else
            (let uu____60238 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____60238)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60242) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____60248 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____60248
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____60252) ->
          let uu____60261 =
            let uu____60263 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____60263 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____60261
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
            | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                -> failwith "impossible"
            | (FStar_Pervasives_Native.Some lift_wp,uu____60308) -> lift_wp
            | (uu____60315,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____60323 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____60323 with
           | (us,t) ->
               let uu____60335 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____60337 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____60339 = univ_names_to_string us  in
               let uu____60341 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____60335
                 uu____60337 uu____60339 uu____60341)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____60353 = FStar_Options.print_universes ()  in
          if uu____60353
          then
            let uu____60357 =
              let uu____60362 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____60362  in
            (match uu____60357 with
             | (univs2,t) ->
                 let uu____60376 =
                   let uu____60381 =
                     let uu____60382 = FStar_Syntax_Subst.compress t  in
                     uu____60382.FStar_Syntax_Syntax.n  in
                   match uu____60381 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____60411 -> failwith "impossible"  in
                 (match uu____60376 with
                  | (tps1,c1) ->
                      let uu____60420 = sli l  in
                      let uu____60422 = univ_names_to_string univs2  in
                      let uu____60424 = binders_to_string " " tps1  in
                      let uu____60427 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____60420
                        uu____60422 uu____60424 uu____60427))
          else
            (let uu____60432 = sli l  in
             let uu____60434 = binders_to_string " " tps  in
             let uu____60437 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____60432 uu____60434
               uu____60437)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____60446 =
            let uu____60448 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____60448  in
          let uu____60458 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____60446 uu____60458
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____60462 ->
        let uu____60465 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____60465 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____60482 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____60482 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____60493,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____60495;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____60497;
                        FStar_Syntax_Syntax.lbdef = uu____60498;
                        FStar_Syntax_Syntax.lbattrs = uu____60499;
                        FStar_Syntax_Syntax.lbpos = uu____60500;_}::[]),uu____60501)
        ->
        let uu____60524 = lbname_to_string lb  in
        let uu____60526 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____60524 uu____60526
    | uu____60529 ->
        let uu____60530 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____60530 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____60554 = sli m.FStar_Syntax_Syntax.name  in
    let uu____60556 =
      let uu____60558 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____60558 (FStar_String.concat "\n")  in
    let uu____60568 =
      let uu____60570 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____60570 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____60554
      uu____60556 uu____60568
  
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
          (let uu____60614 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____60614))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____60623 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____60623)));
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
           (let uu____60664 = f x  in
            FStar_Util.string_builder_append strb uu____60664);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____60673 = f x1  in
                 FStar_Util.string_builder_append strb uu____60673)) xs;
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
           (let uu____60720 = f x  in
            FStar_Util.string_builder_append strb uu____60720);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____60729 = f x1  in
                 FStar_Util.string_builder_append strb uu____60729)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____60751 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____60751
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_60764  ->
    match uu___442_60764 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____60780 =
          let uu____60782 =
            let uu____60784 =
              let uu____60786 =
                let uu____60788 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____60788 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____60786 ")"  in
            Prims.op_Hat " " uu____60784  in
          Prims.op_Hat h uu____60782  in
        Prims.op_Hat "(" uu____60780
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____60803 =
          let uu____60805 = emb_typ_to_string a  in
          let uu____60807 =
            let uu____60809 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____60809  in
          Prims.op_Hat uu____60805 uu____60807  in
        Prims.op_Hat "(" uu____60803
  