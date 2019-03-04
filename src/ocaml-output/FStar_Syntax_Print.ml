open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_56157  ->
    match uu___429_56157 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____56161 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____56161
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____56166 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____56166
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____56170 =
          let uu____56172 = delta_depth_to_string d  in
          Prims.op_Hat uu____56172 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____56170
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____56184 = FStar_Options.print_real_names ()  in
    if uu____56184
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56211 =
      let uu____56213 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____56213  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56211
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56223 = FStar_Options.print_real_names ()  in
    if uu____56223
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56236 =
      let uu____56238 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____56238  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56236
  
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
      | uu____56460 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____56473 -> failwith "get_lid"
  
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
  'Auu____56576 'Auu____56577 .
    ('Auu____56576,'Auu____56577) FStar_Util.either -> Prims.bool
  =
  fun uu___430_56587  ->
    match uu___430_56587 with
    | FStar_Util.Inl uu____56592 -> false
    | FStar_Util.Inr uu____56594 -> true
  
let filter_imp :
  'Auu____56601 .
    ('Auu____56601 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____56601 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_56656  ->
            match uu___431_56656 with
            | (uu____56664,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____56671,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____56672)) -> false
            | (uu____56677,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____56678)) -> false
            | uu____56684 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____56702 =
      let uu____56703 = FStar_Syntax_Subst.compress e  in
      uu____56703.FStar_Syntax_Syntax.n  in
    match uu____56702 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____56764 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____56764
        then
          let uu____56773 =
            let uu____56778 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____56778  in
          (match uu____56773 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____56789 =
                 let uu____56792 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____56792 :: xs  in
               FStar_Pervasives_Native.Some uu____56789
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____56804 ->
        let uu____56805 = is_lex_top e  in
        if uu____56805
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____56853 = f hd1  in if uu____56853 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____56885 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____56885
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56916 = get_lid e  in find_lid uu____56916 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56928 = get_lid e  in find_lid uu____56928 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____56940 = get_lid t  in find_lid uu____56940 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_56954  ->
    match uu___432_56954 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____56965 = FStar_Options.hide_uvar_nums ()  in
    if uu____56965
    then "?"
    else
      (let uu____56972 =
         let uu____56974 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____56974 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____56972)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____56986 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____56988 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____56986 uu____56988
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____57014 = FStar_Options.hide_uvar_nums ()  in
    if uu____57014
    then "?"
    else
      (let uu____57021 =
         let uu____57023 =
           let uu____57025 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____57025 FStar_Util.string_of_int  in
         let uu____57029 =
           let uu____57031 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____57031  in
         Prims.op_Hat uu____57023 uu____57029  in
       Prims.op_Hat "?" uu____57021)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____57059 = FStar_Syntax_Subst.compress_univ u  in
      match uu____57059 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____57072 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____57083 = FStar_Syntax_Subst.compress_univ u  in
    match uu____57083 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____57094 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____57094
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____57101 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____57101
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____57106 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____57106 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____57127 = univ_to_string u2  in
             let uu____57129 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____57127 uu____57129)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____57135 =
          let uu____57137 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____57137 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____57135
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____57156 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____57156 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____57173 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____57173 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_57191  ->
    match uu___433_57191 with
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
        let uu____57207 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____57207
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____57212 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____57212
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____57225 =
          let uu____57227 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57227  in
        let uu____57228 =
          let uu____57230 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57230 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____57225 uu____57228
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____57256 =
          let uu____57258 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57258  in
        let uu____57259 =
          let uu____57261 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57261 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____57256
          uu____57259
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____57278 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____57278
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
    | uu____57301 ->
        let uu____57304 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____57304 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____57332 ->
        let uu____57335 = quals_to_string quals  in
        Prims.op_Hat uu____57335 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____57531 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____57531
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____57535 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____57535
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____57539 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____57539
    | FStar_Syntax_Syntax.Tm_uinst uu____57542 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____57550 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____57552 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57554,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____57555;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57569,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____57570;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____57584 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____57604 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____57620 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____57628 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____57646 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____57670 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____57698 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____57713 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____57727,m) ->
        let uu____57765 = FStar_ST.op_Bang m  in
        (match uu____57765 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____57823 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____57829,m) ->
        let uu____57835 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____57835
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____57839 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____57842 =
      let uu____57844 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____57844  in
    if uu____57842
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____57858 = FStar_Options.print_implicits ()  in
         if uu____57858 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____57866 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____57891,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____57917,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____57919;
             FStar_Syntax_Syntax.rng = uu____57920;_}
           ->
           let uu____57931 =
             let uu____57933 =
               let uu____57935 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____57935  in
             Prims.op_Hat uu____57933 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____57931
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____57981 =
             let uu____57983 =
               let uu____57985 =
                 let uu____57986 =
                   let uu____57995 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____57995  in
                 uu____57986 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____57985  in
             Prims.op_Hat uu____57983 "]"  in
           Prims.op_Hat "[lazy:" uu____57981
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____58064 =
                  match uu____58064 with
                  | (bv,t) ->
                      let uu____58072 = bv_to_string bv  in
                      let uu____58074 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____58072 uu____58074
                   in
                let uu____58077 = term_to_string tm  in
                let uu____58079 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____58077 uu____58079
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____58088 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____58088)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____58111 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____58148 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____58173  ->
                                 match uu____58173 with
                                 | (t1,uu____58182) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____58148
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____58111 (FStar_String.concat "\\/")  in
           let uu____58197 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____58197
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____58211 = tag_of_term t  in
           let uu____58213 = sli m  in
           let uu____58215 = term_to_string t'  in
           let uu____58217 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____58211
             uu____58213 uu____58215 uu____58217
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____58232 = tag_of_term t  in
           let uu____58234 = term_to_string t'  in
           let uu____58236 = sli m0  in
           let uu____58238 = sli m1  in
           let uu____58240 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____58232 uu____58234 uu____58236 uu____58238 uu____58240
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____58255 = FStar_Range.string_of_range r  in
           let uu____58257 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____58255
             uu____58257
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____58266 = lid_to_string l  in
           let uu____58268 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____58270 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____58266
             uu____58268 uu____58270
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____58274) ->
           let uu____58279 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____58279
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____58283 = db_to_string x3  in
           let uu____58285 =
             let uu____58287 =
               let uu____58289 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____58289 ")"  in
             Prims.op_Hat ":(" uu____58287  in
           Prims.op_Hat uu____58283 uu____58285
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____58296)) ->
           let uu____58311 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58311
           then ctx_uvar_to_string u
           else
             (let uu____58317 =
                let uu____58319 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58319  in
              Prims.op_Hat "?" uu____58317)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____58342 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58342
           then
             let uu____58346 = ctx_uvar_to_string u  in
             let uu____58348 =
               let uu____58350 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____58350 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____58346 uu____58348
           else
             (let uu____58369 =
                let uu____58371 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58371  in
              Prims.op_Hat "?" uu____58369)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____58378 = FStar_Options.print_universes ()  in
           if uu____58378
           then
             let uu____58382 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____58382
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____58410 = binders_to_string " -> " bs  in
           let uu____58413 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____58410 uu____58413
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____58445 = binders_to_string " " bs  in
                let uu____58448 = term_to_string t2  in
                let uu____58450 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____58459 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____58459)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____58445 uu____58448
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____58450
            | uu____58463 ->
                let uu____58466 = binders_to_string " " bs  in
                let uu____58469 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____58466 uu____58469)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____58478 = bv_to_string xt  in
           let uu____58480 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____58483 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____58478 uu____58480
             uu____58483
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____58515 = term_to_string t  in
           let uu____58517 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____58515 uu____58517
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____58540 = lbs_to_string [] lbs  in
           let uu____58542 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____58540 uu____58542
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____58607 =
                   let uu____58609 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____58609
                     (FStar_Util.dflt "default")
                    in
                 let uu____58620 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____58607 uu____58620
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____58641 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____58641
              in
           let uu____58644 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____58644 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____58685 = term_to_string head1  in
           let uu____58687 =
             let uu____58689 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____58722  ->
                       match uu____58722 with
                       | (p,wopt,e) ->
                           let uu____58739 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____58742 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____58747 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____58747
                              in
                           let uu____58751 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____58739
                             uu____58742 uu____58751))
                in
             FStar_Util.concat_l "\n\t|" uu____58689  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____58685
             uu____58687
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____58763 = FStar_Options.print_universes ()  in
           if uu____58763
           then
             let uu____58767 = term_to_string t  in
             let uu____58769 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____58767 uu____58769
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____58776 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____58779 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____58781 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____58776 uu____58779
      uu____58781

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_58784  ->
    match uu___434_58784 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____58790 = FStar_Util.string_of_int i  in
        let uu____58792 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____58790 uu____58792
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____58799 = bv_to_string x  in
        let uu____58801 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____58799 uu____58801
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____58810 = bv_to_string x  in
        let uu____58812 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____58810 uu____58812
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____58819 = FStar_Util.string_of_int i  in
        let uu____58821 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____58819 uu____58821
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____58828 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____58828

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____58832 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____58832 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____58848 =
      let uu____58850 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____58850  in
    if uu____58848
    then
      let e =
        let uu____58855 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____58855  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____58884 = fv_to_string l  in
           let uu____58886 =
             let uu____58888 =
               FStar_List.map
                 (fun uu____58902  ->
                    match uu____58902 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____58888 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____58884 uu____58886
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____58927) ->
           let uu____58932 = FStar_Options.print_bound_var_types ()  in
           if uu____58932
           then
             let uu____58936 = bv_to_string x1  in
             let uu____58938 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____58936 uu____58938
           else
             (let uu____58943 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____58943)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____58947 = FStar_Options.print_bound_var_types ()  in
           if uu____58947
           then
             let uu____58951 = bv_to_string x1  in
             let uu____58953 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____58951 uu____58953
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____58960 = FStar_Options.print_bound_var_types ()  in
           if uu____58960
           then
             let uu____58964 = bv_to_string x1  in
             let uu____58966 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____58964 uu____58966
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____58975 = quals_to_string' quals  in
      let uu____58977 =
        let uu____58979 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____58999 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____59001 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____59003 =
                    let uu____59005 = FStar_Options.print_universes ()  in
                    if uu____59005
                    then
                      let uu____59009 =
                        let uu____59011 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____59011 ">"  in
                      Prims.op_Hat "<" uu____59009
                    else ""  in
                  let uu____59018 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____59020 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____58999
                    uu____59001 uu____59003 uu____59018 uu____59020))
           in
        FStar_Util.concat_l "\n and " uu____58979  in
      FStar_Util.format3 "%slet %s %s" uu____58975
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____58977

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_59035  ->
    match uu___435_59035 with
    | [] -> ""
    | tms ->
        let uu____59043 =
          let uu____59045 =
            FStar_List.map
              (fun t  ->
                 let uu____59053 = term_to_string t  in paren uu____59053)
              tms
             in
          FStar_All.pipe_right uu____59045 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____59043

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____59062 = FStar_Options.print_effect_args ()  in
    if uu____59062
    then
      let uu____59066 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____59066
    else
      (let uu____59069 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____59071 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____59069 uu____59071)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_59075  ->
      match uu___436_59075 with
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
          let uu____59093 =
            let uu____59095 = term_to_string t  in
            Prims.op_Hat uu____59095 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____59093
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
      let uu____59115 =
        let uu____59117 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____59117  in
      if uu____59115
      then
        let uu____59121 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____59121 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____59132 = b  in
         match uu____59132 with
         | (a,imp) ->
             let uu____59146 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____59146
             then
               let uu____59150 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____59150
             else
               (let uu____59155 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____59158 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____59158)
                   in
                if uu____59155
                then
                  let uu____59162 = nm_to_string a  in
                  imp_to_string uu____59162 imp
                else
                  (let uu____59166 =
                     let uu____59168 = nm_to_string a  in
                     let uu____59170 =
                       let uu____59172 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____59172  in
                     Prims.op_Hat uu____59168 uu____59170  in
                   imp_to_string uu____59166 imp)))

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
        let uu____59191 = FStar_Options.print_implicits ()  in
        if uu____59191 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____59202 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____59202 (FStar_String.concat sep)
      else
        (let uu____59230 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____59230 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_59244  ->
    match uu___437_59244 with
    | (a,imp) ->
        let uu____59258 = term_to_string a  in imp_to_string uu____59258 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____59270 = FStar_Options.print_implicits ()  in
      if uu____59270 then args else filter_imp args  in
    let uu____59285 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59285 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____59314 = FStar_Options.ugly ()  in
      if uu____59314
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____59325 =
      let uu____59327 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59327  in
    if uu____59325
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____59348 =
             let uu____59349 = FStar_Syntax_Subst.compress t  in
             uu____59349.FStar_Syntax_Syntax.n  in
           (match uu____59348 with
            | FStar_Syntax_Syntax.Tm_type uu____59353 when
                let uu____59354 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59354 -> term_to_string t
            | uu____59356 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59359 = univ_to_string u  in
                     let uu____59361 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____59359 uu____59361
                 | uu____59364 ->
                     let uu____59367 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____59367))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____59380 =
             let uu____59381 = FStar_Syntax_Subst.compress t  in
             uu____59381.FStar_Syntax_Syntax.n  in
           (match uu____59380 with
            | FStar_Syntax_Syntax.Tm_type uu____59385 when
                let uu____59386 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59386 -> term_to_string t
            | uu____59388 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59391 = univ_to_string u  in
                     let uu____59393 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____59391 uu____59393
                 | uu____59396 ->
                     let uu____59399 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____59399))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____59405 = FStar_Options.print_effect_args ()  in
             if uu____59405
             then
               let uu____59409 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____59411 =
                 let uu____59413 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____59413 (FStar_String.concat ", ")
                  in
               let uu____59428 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____59430 =
                 let uu____59432 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____59432 (FStar_String.concat ", ")
                  in
               let uu____59459 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____59409 uu____59411 uu____59428 uu____59430 uu____59459
             else
               (let uu____59464 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_59470  ->
                           match uu___438_59470 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____59473 -> false)))
                    &&
                    (let uu____59476 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____59476)
                   in
                if uu____59464
                then
                  let uu____59480 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____59480
                else
                  (let uu____59485 =
                     ((let uu____59489 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____59489) &&
                        (let uu____59492 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____59492))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____59485
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____59498 =
                        (let uu____59502 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____59502) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_59508  ->
                                   match uu___439_59508 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____59511 -> false)))
                         in
                      if uu____59498
                      then
                        let uu____59515 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____59515
                      else
                        (let uu____59520 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____59522 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____59520 uu____59522))))
              in
           let dec =
             let uu____59527 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_59540  ->
                       match uu___440_59540 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____59547 =
                             let uu____59549 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____59549
                              in
                           [uu____59547]
                       | uu____59554 -> []))
                in
             FStar_All.pipe_right uu____59527 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____59573 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_59583  ->
    match uu___441_59583 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____59600 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____59637 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____59662  ->
                              match uu____59662 with
                              | (t,uu____59671) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____59637
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____59600 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____59688 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____59688
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____59693) ->
        let uu____59698 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____59698
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____59709 = sli m  in
        let uu____59711 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____59709 uu____59711
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____59721 = sli m  in
        let uu____59723 = sli m'  in
        let uu____59725 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____59721
          uu____59723 uu____59725

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____59740 = FStar_Options.ugly ()  in
      if uu____59740
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
      let uu____59761 = b  in
      match uu____59761 with
      | (a,imp) ->
          let n1 =
            let uu____59769 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____59769
            then FStar_Util.JsonNull
            else
              (let uu____59774 =
                 let uu____59776 = nm_to_string a  in
                 imp_to_string uu____59776 imp  in
               FStar_Util.JsonStr uu____59774)
             in
          let t =
            let uu____59779 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____59779  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____59811 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____59811
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____59829 = FStar_Options.print_universes ()  in
    if uu____59829 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____59845 =
      let uu____59847 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59847  in
    if uu____59845
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____59857 = s  in
       match uu____59857 with
       | (us,t) ->
           let uu____59869 =
             let uu____59871 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____59871  in
           let uu____59875 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____59869 uu____59875)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____59885 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____59887 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____59890 =
      let uu____59892 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____59892  in
    let uu____59896 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____59898 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____59885 uu____59887
      uu____59890 uu____59896 uu____59898
  
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
          let uu____59929 =
            let uu____59931 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____59931  in
          if uu____59929
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____59952 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____59952 (FStar_String.concat ",\n\t")
                in
             let uu____59967 =
               let uu____59971 =
                 let uu____59975 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____59977 =
                   let uu____59981 =
                     let uu____59983 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____59983  in
                   let uu____59987 =
                     let uu____59991 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____59994 =
                       let uu____59998 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____60000 =
                         let uu____60004 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____60006 =
                           let uu____60010 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____60012 =
                             let uu____60016 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____60018 =
                               let uu____60022 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____60024 =
                                 let uu____60028 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____60030 =
                                   let uu____60034 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____60036 =
                                     let uu____60040 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____60042 =
                                       let uu____60046 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____60048 =
                                         let uu____60052 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____60054 =
                                           let uu____60058 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____60060 =
                                             let uu____60064 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____60066 =
                                               let uu____60070 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____60072 =
                                                 let uu____60076 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____60078 =
                                                   let uu____60082 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____60082]  in
                                                 uu____60076 :: uu____60078
                                                  in
                                               uu____60070 :: uu____60072  in
                                             uu____60064 :: uu____60066  in
                                           uu____60058 :: uu____60060  in
                                         uu____60052 :: uu____60054  in
                                       uu____60046 :: uu____60048  in
                                     uu____60040 :: uu____60042  in
                                   uu____60034 :: uu____60036  in
                                 uu____60028 :: uu____60030  in
                               uu____60022 :: uu____60024  in
                             uu____60016 :: uu____60018  in
                           uu____60010 :: uu____60012  in
                         uu____60004 :: uu____60006  in
                       uu____59998 :: uu____60000  in
                     uu____59991 :: uu____59994  in
                   uu____59981 :: uu____59987  in
                 uu____59975 :: uu____59977  in
               (if for_free then "_for_free " else "") :: uu____59971  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____59967)
  
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
          (lid,univs1,tps,k,uu____60156,uu____60157) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____60173 = FStar_Options.print_universes ()  in
          if uu____60173
          then
            let uu____60177 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____60177 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____60186,uu____60187,uu____60188) ->
          let uu____60195 = FStar_Options.print_universes ()  in
          if uu____60195
          then
            let uu____60199 = univ_names_to_string univs1  in
            let uu____60201 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____60199
              lid.FStar_Ident.str uu____60201
          else
            (let uu____60206 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____60206)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____60212 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____60214 =
            let uu____60216 = FStar_Options.print_universes ()  in
            if uu____60216
            then
              let uu____60220 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____60220
            else ""  in
          let uu____60226 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____60212
            lid.FStar_Ident.str uu____60214 uu____60226
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____60232 = FStar_Options.print_universes ()  in
          if uu____60232
          then
            let uu____60236 = univ_names_to_string us  in
            let uu____60238 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____60236 uu____60238
          else
            (let uu____60243 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____60243)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60247) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____60253 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____60253
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____60257) ->
          let uu____60266 =
            let uu____60268 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____60268 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____60266
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____60313) -> lift_wp
            | (uu____60320,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____60328 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____60328 with
           | (us,t) ->
               let uu____60340 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____60342 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____60344 = univ_names_to_string us  in
               let uu____60346 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____60340
                 uu____60342 uu____60344 uu____60346)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____60358 = FStar_Options.print_universes ()  in
          if uu____60358
          then
            let uu____60362 =
              let uu____60367 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____60367  in
            (match uu____60362 with
             | (univs2,t) ->
                 let uu____60381 =
                   let uu____60386 =
                     let uu____60387 = FStar_Syntax_Subst.compress t  in
                     uu____60387.FStar_Syntax_Syntax.n  in
                   match uu____60386 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____60416 -> failwith "impossible"  in
                 (match uu____60381 with
                  | (tps1,c1) ->
                      let uu____60425 = sli l  in
                      let uu____60427 = univ_names_to_string univs2  in
                      let uu____60429 = binders_to_string " " tps1  in
                      let uu____60432 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____60425
                        uu____60427 uu____60429 uu____60432))
          else
            (let uu____60437 = sli l  in
             let uu____60439 = binders_to_string " " tps  in
             let uu____60442 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____60437 uu____60439
               uu____60442)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____60451 =
            let uu____60453 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____60453  in
          let uu____60463 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____60451 uu____60463
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____60467 ->
        let uu____60470 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____60470 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____60487 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____60487 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____60498,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____60500;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____60502;
                        FStar_Syntax_Syntax.lbdef = uu____60503;
                        FStar_Syntax_Syntax.lbattrs = uu____60504;
                        FStar_Syntax_Syntax.lbpos = uu____60505;_}::[]),uu____60506)
        ->
        let uu____60529 = lbname_to_string lb  in
        let uu____60531 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____60529 uu____60531
    | uu____60534 ->
        let uu____60535 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____60535 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____60559 = sli m.FStar_Syntax_Syntax.name  in
    let uu____60561 =
      let uu____60563 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____60563 (FStar_String.concat "\n")  in
    let uu____60573 =
      let uu____60575 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____60575 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____60559
      uu____60561 uu____60573
  
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
          (let uu____60619 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____60619))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____60628 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____60628)));
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
           (let uu____60669 = f x  in
            FStar_Util.string_builder_append strb uu____60669);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____60678 = f x1  in
                 FStar_Util.string_builder_append strb uu____60678)) xs;
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
           (let uu____60725 = f x  in
            FStar_Util.string_builder_append strb uu____60725);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____60734 = f x1  in
                 FStar_Util.string_builder_append strb uu____60734)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____60756 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____60756
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_60769  ->
    match uu___442_60769 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____60785 =
          let uu____60787 =
            let uu____60789 =
              let uu____60791 =
                let uu____60793 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____60793 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____60791 ")"  in
            Prims.op_Hat " " uu____60789  in
          Prims.op_Hat h uu____60787  in
        Prims.op_Hat "(" uu____60785
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____60808 =
          let uu____60810 = emb_typ_to_string a  in
          let uu____60812 =
            let uu____60814 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____60814  in
          Prims.op_Hat uu____60810 uu____60812  in
        Prims.op_Hat "(" uu____60808
  