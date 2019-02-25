open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_56074  ->
    match uu___429_56074 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____56078 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____56078
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____56083 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____56083
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____56087 =
          let uu____56089 = delta_depth_to_string d  in
          Prims.op_Hat uu____56089 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____56087
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____56101 = FStar_Options.print_real_names ()  in
    if uu____56101
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56128 =
      let uu____56130 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____56130  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56128
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56140 = FStar_Options.print_real_names ()  in
    if uu____56140
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56153 =
      let uu____56155 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____56155  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56153
  
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
      | uu____56377 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____56390 -> failwith "get_lid"
  
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
  'Auu____56493 'Auu____56494 .
    ('Auu____56493,'Auu____56494) FStar_Util.either -> Prims.bool
  =
  fun uu___430_56504  ->
    match uu___430_56504 with
    | FStar_Util.Inl uu____56509 -> false
    | FStar_Util.Inr uu____56511 -> true
  
let filter_imp :
  'Auu____56518 .
    ('Auu____56518 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____56518 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_56573  ->
            match uu___431_56573 with
            | (uu____56581,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____56588,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____56589)) -> false
            | (uu____56594,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____56595)) -> false
            | uu____56601 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____56619 =
      let uu____56620 = FStar_Syntax_Subst.compress e  in
      uu____56620.FStar_Syntax_Syntax.n  in
    match uu____56619 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____56681 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____56681
        then
          let uu____56690 =
            let uu____56695 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____56695  in
          (match uu____56690 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____56706 =
                 let uu____56709 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____56709 :: xs  in
               FStar_Pervasives_Native.Some uu____56706
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____56721 ->
        let uu____56722 = is_lex_top e  in
        if uu____56722
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____56770 = f hd1  in if uu____56770 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____56802 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____56802
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56833 = get_lid e  in find_lid uu____56833 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56845 = get_lid e  in find_lid uu____56845 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____56857 = get_lid t  in find_lid uu____56857 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_56871  ->
    match uu___432_56871 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____56882 = FStar_Options.hide_uvar_nums ()  in
    if uu____56882
    then "?"
    else
      (let uu____56889 =
         let uu____56891 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____56891 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____56889)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____56903 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____56905 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____56903 uu____56905
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____56931 = FStar_Options.hide_uvar_nums ()  in
    if uu____56931
    then "?"
    else
      (let uu____56938 =
         let uu____56940 =
           let uu____56942 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____56942 FStar_Util.string_of_int  in
         let uu____56946 =
           let uu____56948 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____56948  in
         Prims.op_Hat uu____56940 uu____56946  in
       Prims.op_Hat "?" uu____56938)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____56976 = FStar_Syntax_Subst.compress_univ u  in
      match uu____56976 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____56989 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____57000 = FStar_Syntax_Subst.compress_univ u  in
    match uu____57000 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____57011 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____57011
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____57018 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____57018
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____57023 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____57023 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____57044 = univ_to_string u2  in
             let uu____57046 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____57044 uu____57046)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____57052 =
          let uu____57054 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____57054 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____57052
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____57073 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____57073 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____57090 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____57090 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_57108  ->
    match uu___433_57108 with
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
        let uu____57124 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____57124
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____57129 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____57129
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____57142 =
          let uu____57144 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57144  in
        let uu____57145 =
          let uu____57147 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57147 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____57142 uu____57145
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____57173 =
          let uu____57175 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57175  in
        let uu____57176 =
          let uu____57178 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57178 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____57173
          uu____57176
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____57195 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____57195
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
    | uu____57218 ->
        let uu____57221 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____57221 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____57249 ->
        let uu____57252 = quals_to_string quals  in
        Prims.op_Hat uu____57252 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____57448 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____57448
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____57452 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____57452
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____57456 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____57456
    | FStar_Syntax_Syntax.Tm_uinst uu____57459 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____57467 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____57469 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57471,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____57472;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57486,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____57487;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____57501 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____57521 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____57537 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____57545 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____57563 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____57587 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____57615 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____57630 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____57644,m) ->
        let uu____57682 = FStar_ST.op_Bang m  in
        (match uu____57682 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____57740 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____57746,m) ->
        let uu____57752 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____57752
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____57756 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____57759 =
      let uu____57761 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____57761  in
    if uu____57759
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____57775 = FStar_Options.print_implicits ()  in
         if uu____57775 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____57783 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____57808,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____57834,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____57836;
             FStar_Syntax_Syntax.rng = uu____57837;_}
           ->
           let uu____57848 =
             let uu____57850 =
               let uu____57852 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____57852  in
             Prims.op_Hat uu____57850 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____57848
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____57898 =
             let uu____57900 =
               let uu____57902 =
                 let uu____57903 =
                   let uu____57912 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____57912  in
                 uu____57903 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____57902  in
             Prims.op_Hat uu____57900 "]"  in
           Prims.op_Hat "[lazy:" uu____57898
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____57981 =
                  match uu____57981 with
                  | (bv,t) ->
                      let uu____57989 = bv_to_string bv  in
                      let uu____57991 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____57989 uu____57991
                   in
                let uu____57994 = term_to_string tm  in
                let uu____57996 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____57994 uu____57996
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____58005 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____58005)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____58028 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____58065 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____58090  ->
                                 match uu____58090 with
                                 | (t1,uu____58099) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____58065
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____58028 (FStar_String.concat "\\/")  in
           let uu____58114 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____58114
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____58128 = tag_of_term t  in
           let uu____58130 = sli m  in
           let uu____58132 = term_to_string t'  in
           let uu____58134 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____58128
             uu____58130 uu____58132 uu____58134
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____58149 = tag_of_term t  in
           let uu____58151 = term_to_string t'  in
           let uu____58153 = sli m0  in
           let uu____58155 = sli m1  in
           let uu____58157 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____58149 uu____58151 uu____58153 uu____58155 uu____58157
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____58172 = FStar_Range.string_of_range r  in
           let uu____58174 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____58172
             uu____58174
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____58183 = lid_to_string l  in
           let uu____58185 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____58187 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____58183
             uu____58185 uu____58187
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____58191) ->
           let uu____58196 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____58196
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____58200 = db_to_string x3  in
           let uu____58202 =
             let uu____58204 =
               let uu____58206 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____58206 ")"  in
             Prims.op_Hat ":(" uu____58204  in
           Prims.op_Hat uu____58200 uu____58202
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____58213)) ->
           let uu____58228 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58228
           then ctx_uvar_to_string u
           else
             (let uu____58234 =
                let uu____58236 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58236  in
              Prims.op_Hat "?" uu____58234)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____58259 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58259
           then
             let uu____58263 = ctx_uvar_to_string u  in
             let uu____58265 =
               let uu____58267 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____58267 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____58263 uu____58265
           else
             (let uu____58286 =
                let uu____58288 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58288  in
              Prims.op_Hat "?" uu____58286)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____58295 = FStar_Options.print_universes ()  in
           if uu____58295
           then
             let uu____58299 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____58299
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____58327 = binders_to_string " -> " bs  in
           let uu____58330 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____58327 uu____58330
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____58362 = binders_to_string " " bs  in
                let uu____58365 = term_to_string t2  in
                let uu____58367 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____58376 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____58376)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____58362 uu____58365
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____58367
            | uu____58380 ->
                let uu____58383 = binders_to_string " " bs  in
                let uu____58386 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____58383 uu____58386)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____58395 = bv_to_string xt  in
           let uu____58397 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____58400 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____58395 uu____58397
             uu____58400
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____58432 = term_to_string t  in
           let uu____58434 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____58432 uu____58434
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____58457 = lbs_to_string [] lbs  in
           let uu____58459 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____58457 uu____58459
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____58524 =
                   let uu____58526 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____58526
                     (FStar_Util.dflt "default")
                    in
                 let uu____58537 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____58524 uu____58537
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____58558 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____58558
              in
           let uu____58561 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____58561 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____58602 = term_to_string head1  in
           let uu____58604 =
             let uu____58606 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____58639  ->
                       match uu____58639 with
                       | (p,wopt,e) ->
                           let uu____58656 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____58659 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____58664 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____58664
                              in
                           let uu____58668 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____58656
                             uu____58659 uu____58668))
                in
             FStar_Util.concat_l "\n\t|" uu____58606  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____58602
             uu____58604
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____58680 = FStar_Options.print_universes ()  in
           if uu____58680
           then
             let uu____58684 = term_to_string t  in
             let uu____58686 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____58684 uu____58686
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____58693 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____58696 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____58698 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____58693 uu____58696
      uu____58698

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_58701  ->
    match uu___434_58701 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____58707 = FStar_Util.string_of_int i  in
        let uu____58709 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____58707 uu____58709
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____58716 = bv_to_string x  in
        let uu____58718 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____58716 uu____58718
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____58727 = bv_to_string x  in
        let uu____58729 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____58727 uu____58729
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____58736 = FStar_Util.string_of_int i  in
        let uu____58738 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____58736 uu____58738
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____58745 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____58745

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____58749 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____58749 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____58765 =
      let uu____58767 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____58767  in
    if uu____58765
    then
      let e =
        let uu____58772 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____58772  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____58801 = fv_to_string l  in
           let uu____58803 =
             let uu____58805 =
               FStar_List.map
                 (fun uu____58819  ->
                    match uu____58819 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____58805 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____58801 uu____58803
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____58844) ->
           let uu____58849 = FStar_Options.print_bound_var_types ()  in
           if uu____58849
           then
             let uu____58853 = bv_to_string x1  in
             let uu____58855 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____58853 uu____58855
           else
             (let uu____58860 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____58860)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____58864 = FStar_Options.print_bound_var_types ()  in
           if uu____58864
           then
             let uu____58868 = bv_to_string x1  in
             let uu____58870 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____58868 uu____58870
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____58877 = FStar_Options.print_bound_var_types ()  in
           if uu____58877
           then
             let uu____58881 = bv_to_string x1  in
             let uu____58883 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____58881 uu____58883
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____58892 = quals_to_string' quals  in
      let uu____58894 =
        let uu____58896 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____58916 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____58918 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____58920 =
                    let uu____58922 = FStar_Options.print_universes ()  in
                    if uu____58922
                    then
                      let uu____58926 =
                        let uu____58928 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____58928 ">"  in
                      Prims.op_Hat "<" uu____58926
                    else ""  in
                  let uu____58935 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____58937 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____58916
                    uu____58918 uu____58920 uu____58935 uu____58937))
           in
        FStar_Util.concat_l "\n and " uu____58896  in
      FStar_Util.format3 "%slet %s %s" uu____58892
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____58894

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_58952  ->
    match uu___435_58952 with
    | [] -> ""
    | tms ->
        let uu____58960 =
          let uu____58962 =
            FStar_List.map
              (fun t  ->
                 let uu____58970 = term_to_string t  in paren uu____58970)
              tms
             in
          FStar_All.pipe_right uu____58962 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____58960

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____58979 = FStar_Options.print_effect_args ()  in
    if uu____58979
    then
      let uu____58983 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____58983
    else
      (let uu____58986 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____58988 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____58986 uu____58988)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_58992  ->
      match uu___436_58992 with
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
          let uu____59010 =
            let uu____59012 = term_to_string t  in
            Prims.op_Hat uu____59012 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____59010
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
      let uu____59032 =
        let uu____59034 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____59034  in
      if uu____59032
      then
        let uu____59038 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____59038 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____59049 = b  in
         match uu____59049 with
         | (a,imp) ->
             let uu____59063 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____59063
             then
               let uu____59067 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____59067
             else
               (let uu____59072 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____59075 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____59075)
                   in
                if uu____59072
                then
                  let uu____59079 = nm_to_string a  in
                  imp_to_string uu____59079 imp
                else
                  (let uu____59083 =
                     let uu____59085 = nm_to_string a  in
                     let uu____59087 =
                       let uu____59089 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____59089  in
                     Prims.op_Hat uu____59085 uu____59087  in
                   imp_to_string uu____59083 imp)))

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
        let uu____59108 = FStar_Options.print_implicits ()  in
        if uu____59108 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____59119 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____59119 (FStar_String.concat sep)
      else
        (let uu____59147 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____59147 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_59161  ->
    match uu___437_59161 with
    | (a,imp) ->
        let uu____59175 = term_to_string a  in imp_to_string uu____59175 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____59187 = FStar_Options.print_implicits ()  in
      if uu____59187 then args else filter_imp args  in
    let uu____59202 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59202 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____59231 = FStar_Options.ugly ()  in
      if uu____59231
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____59242 =
      let uu____59244 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59244  in
    if uu____59242
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____59265 =
             let uu____59266 = FStar_Syntax_Subst.compress t  in
             uu____59266.FStar_Syntax_Syntax.n  in
           (match uu____59265 with
            | FStar_Syntax_Syntax.Tm_type uu____59270 when
                let uu____59271 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59271 -> term_to_string t
            | uu____59273 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59276 = univ_to_string u  in
                     let uu____59278 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____59276 uu____59278
                 | uu____59281 ->
                     let uu____59284 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____59284))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____59297 =
             let uu____59298 = FStar_Syntax_Subst.compress t  in
             uu____59298.FStar_Syntax_Syntax.n  in
           (match uu____59297 with
            | FStar_Syntax_Syntax.Tm_type uu____59302 when
                let uu____59303 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59303 -> term_to_string t
            | uu____59305 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59308 = univ_to_string u  in
                     let uu____59310 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____59308 uu____59310
                 | uu____59313 ->
                     let uu____59316 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____59316))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____59322 = FStar_Options.print_effect_args ()  in
             if uu____59322
             then
               let uu____59326 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____59328 =
                 let uu____59330 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____59330 (FStar_String.concat ", ")
                  in
               let uu____59345 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____59347 =
                 let uu____59349 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____59349 (FStar_String.concat ", ")
                  in
               let uu____59376 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____59326 uu____59328 uu____59345 uu____59347 uu____59376
             else
               (let uu____59381 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_59387  ->
                           match uu___438_59387 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____59390 -> false)))
                    &&
                    (let uu____59393 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____59393)
                   in
                if uu____59381
                then
                  let uu____59397 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____59397
                else
                  (let uu____59402 =
                     ((let uu____59406 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____59406) &&
                        (let uu____59409 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____59409))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____59402
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____59415 =
                        (let uu____59419 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____59419) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_59425  ->
                                   match uu___439_59425 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____59428 -> false)))
                         in
                      if uu____59415
                      then
                        let uu____59432 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____59432
                      else
                        (let uu____59437 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____59439 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____59437 uu____59439))))
              in
           let dec =
             let uu____59444 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_59457  ->
                       match uu___440_59457 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____59464 =
                             let uu____59466 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____59466
                              in
                           [uu____59464]
                       | uu____59471 -> []))
                in
             FStar_All.pipe_right uu____59444 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____59490 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_59500  ->
    match uu___441_59500 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____59517 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____59554 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____59579  ->
                              match uu____59579 with
                              | (t,uu____59588) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____59554
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____59517 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____59605 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____59605
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____59610) ->
        let uu____59615 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____59615
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____59626 = sli m  in
        let uu____59628 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____59626 uu____59628
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____59638 = sli m  in
        let uu____59640 = sli m'  in
        let uu____59642 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____59638
          uu____59640 uu____59642

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____59657 = FStar_Options.ugly ()  in
      if uu____59657
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
      let uu____59678 = b  in
      match uu____59678 with
      | (a,imp) ->
          let n1 =
            let uu____59686 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____59686
            then FStar_Util.JsonNull
            else
              (let uu____59691 =
                 let uu____59693 = nm_to_string a  in
                 imp_to_string uu____59693 imp  in
               FStar_Util.JsonStr uu____59691)
             in
          let t =
            let uu____59696 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____59696  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____59728 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____59728
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____59746 = FStar_Options.print_universes ()  in
    if uu____59746 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____59762 =
      let uu____59764 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59764  in
    if uu____59762
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____59774 = s  in
       match uu____59774 with
       | (us,t) ->
           let uu____59786 =
             let uu____59788 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____59788  in
           let uu____59792 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____59786 uu____59792)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____59802 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____59804 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____59807 =
      let uu____59809 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____59809  in
    let uu____59813 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____59815 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____59802 uu____59804
      uu____59807 uu____59813 uu____59815
  
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
          let uu____59846 =
            let uu____59848 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____59848  in
          if uu____59846
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____59869 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____59869 (FStar_String.concat ",\n\t")
                in
             let uu____59884 =
               let uu____59888 =
                 let uu____59892 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____59894 =
                   let uu____59898 =
                     let uu____59900 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____59900  in
                   let uu____59904 =
                     let uu____59908 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____59911 =
                       let uu____59915 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____59917 =
                         let uu____59921 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____59923 =
                           let uu____59927 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____59929 =
                             let uu____59933 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____59935 =
                               let uu____59939 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____59941 =
                                 let uu____59945 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____59947 =
                                   let uu____59951 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____59953 =
                                     let uu____59957 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____59959 =
                                       let uu____59963 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____59965 =
                                         let uu____59969 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____59971 =
                                           let uu____59975 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____59977 =
                                             let uu____59981 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____59983 =
                                               let uu____59987 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____59989 =
                                                 let uu____59993 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____59995 =
                                                   let uu____59999 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____59999]  in
                                                 uu____59993 :: uu____59995
                                                  in
                                               uu____59987 :: uu____59989  in
                                             uu____59981 :: uu____59983  in
                                           uu____59975 :: uu____59977  in
                                         uu____59969 :: uu____59971  in
                                       uu____59963 :: uu____59965  in
                                     uu____59957 :: uu____59959  in
                                   uu____59951 :: uu____59953  in
                                 uu____59945 :: uu____59947  in
                               uu____59939 :: uu____59941  in
                             uu____59933 :: uu____59935  in
                           uu____59927 :: uu____59929  in
                         uu____59921 :: uu____59923  in
                       uu____59915 :: uu____59917  in
                     uu____59908 :: uu____59911  in
                   uu____59898 :: uu____59904  in
                 uu____59892 :: uu____59894  in
               (if for_free then "_for_free " else "") :: uu____59888  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____59884)
  
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
          (lid,univs1,tps,k,uu____60073,uu____60074) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____60090 = FStar_Options.print_universes ()  in
          if uu____60090
          then
            let uu____60094 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____60094 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____60103,uu____60104,uu____60105) ->
          let uu____60112 = FStar_Options.print_universes ()  in
          if uu____60112
          then
            let uu____60116 = univ_names_to_string univs1  in
            let uu____60118 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____60116
              lid.FStar_Ident.str uu____60118
          else
            (let uu____60123 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____60123)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____60129 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____60131 =
            let uu____60133 = FStar_Options.print_universes ()  in
            if uu____60133
            then
              let uu____60137 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____60137
            else ""  in
          let uu____60143 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____60129
            lid.FStar_Ident.str uu____60131 uu____60143
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____60149 = FStar_Options.print_universes ()  in
          if uu____60149
          then
            let uu____60153 = univ_names_to_string us  in
            let uu____60155 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____60153 uu____60155
          else
            (let uu____60160 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____60160)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60164) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____60170 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____60170
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____60174) ->
          let uu____60183 =
            let uu____60185 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____60185 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____60183
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____60230) -> lift_wp
            | (uu____60237,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____60245 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____60245 with
           | (us,t) ->
               let uu____60257 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____60259 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____60261 = univ_names_to_string us  in
               let uu____60263 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____60257
                 uu____60259 uu____60261 uu____60263)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____60275 = FStar_Options.print_universes ()  in
          if uu____60275
          then
            let uu____60279 =
              let uu____60284 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____60284  in
            (match uu____60279 with
             | (univs2,t) ->
                 let uu____60298 =
                   let uu____60303 =
                     let uu____60304 = FStar_Syntax_Subst.compress t  in
                     uu____60304.FStar_Syntax_Syntax.n  in
                   match uu____60303 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____60333 -> failwith "impossible"  in
                 (match uu____60298 with
                  | (tps1,c1) ->
                      let uu____60342 = sli l  in
                      let uu____60344 = univ_names_to_string univs2  in
                      let uu____60346 = binders_to_string " " tps1  in
                      let uu____60349 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____60342
                        uu____60344 uu____60346 uu____60349))
          else
            (let uu____60354 = sli l  in
             let uu____60356 = binders_to_string " " tps  in
             let uu____60359 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____60354 uu____60356
               uu____60359)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____60368 =
            let uu____60370 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____60370  in
          let uu____60380 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____60368 uu____60380
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____60384 ->
        let uu____60387 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____60387 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____60404 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____60404 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____60415,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____60417;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____60419;
                        FStar_Syntax_Syntax.lbdef = uu____60420;
                        FStar_Syntax_Syntax.lbattrs = uu____60421;
                        FStar_Syntax_Syntax.lbpos = uu____60422;_}::[]),uu____60423)
        ->
        let uu____60446 = lbname_to_string lb  in
        let uu____60448 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____60446 uu____60448
    | uu____60451 ->
        let uu____60452 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____60452 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____60476 = sli m.FStar_Syntax_Syntax.name  in
    let uu____60478 =
      let uu____60480 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____60480 (FStar_String.concat "\n")  in
    let uu____60490 =
      let uu____60492 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____60492 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____60476
      uu____60478 uu____60490
  
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
          (let uu____60536 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____60536))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____60545 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____60545)));
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
           (let uu____60586 = f x  in
            FStar_Util.string_builder_append strb uu____60586);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____60595 = f x1  in
                 FStar_Util.string_builder_append strb uu____60595)) xs;
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
           (let uu____60642 = f x  in
            FStar_Util.string_builder_append strb uu____60642);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____60651 = f x1  in
                 FStar_Util.string_builder_append strb uu____60651)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____60673 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____60673
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_60686  ->
    match uu___442_60686 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____60702 =
          let uu____60704 =
            let uu____60706 =
              let uu____60708 =
                let uu____60710 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____60710 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____60708 ")"  in
            Prims.op_Hat " " uu____60706  in
          Prims.op_Hat h uu____60704  in
        Prims.op_Hat "(" uu____60702
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____60725 =
          let uu____60727 = emb_typ_to_string a  in
          let uu____60729 =
            let uu____60731 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____60731  in
          Prims.op_Hat uu____60727 uu____60729  in
        Prims.op_Hat "(" uu____60725
  