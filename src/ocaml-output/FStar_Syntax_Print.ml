open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_56148  ->
    match uu___429_56148 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____56152 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____56152
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____56157 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____56157
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____56161 =
          let uu____56163 = delta_depth_to_string d  in
          Prims.op_Hat uu____56163 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____56161
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____56175 = FStar_Options.print_real_names ()  in
    if uu____56175
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56202 =
      let uu____56204 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____56204  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56202
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56214 = FStar_Options.print_real_names ()  in
    if uu____56214
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56227 =
      let uu____56229 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____56229  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56227
  
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
      | uu____56451 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____56464 -> failwith "get_lid"
  
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
  'Auu____56567 'Auu____56568 .
    ('Auu____56567,'Auu____56568) FStar_Util.either -> Prims.bool
  =
  fun uu___430_56578  ->
    match uu___430_56578 with
    | FStar_Util.Inl uu____56583 -> false
    | FStar_Util.Inr uu____56585 -> true
  
let filter_imp :
  'Auu____56592 .
    ('Auu____56592 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____56592 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_56647  ->
            match uu___431_56647 with
            | (uu____56655,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____56662,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____56663)) -> false
            | (uu____56668,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____56669)) -> false
            | uu____56675 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____56693 =
      let uu____56694 = FStar_Syntax_Subst.compress e  in
      uu____56694.FStar_Syntax_Syntax.n  in
    match uu____56693 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____56755 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____56755
        then
          let uu____56764 =
            let uu____56769 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____56769  in
          (match uu____56764 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____56780 =
                 let uu____56783 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____56783 :: xs  in
               FStar_Pervasives_Native.Some uu____56780
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____56795 ->
        let uu____56796 = is_lex_top e  in
        if uu____56796
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____56844 = f hd1  in if uu____56844 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____56876 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____56876
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56907 = get_lid e  in find_lid uu____56907 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56919 = get_lid e  in find_lid uu____56919 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____56931 = get_lid t  in find_lid uu____56931 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_56945  ->
    match uu___432_56945 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____56956 = FStar_Options.hide_uvar_nums ()  in
    if uu____56956
    then "?"
    else
      (let uu____56963 =
         let uu____56965 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____56965 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____56963)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____56977 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____56979 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____56977 uu____56979
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____57005 = FStar_Options.hide_uvar_nums ()  in
    if uu____57005
    then "?"
    else
      (let uu____57012 =
         let uu____57014 =
           let uu____57016 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____57016 FStar_Util.string_of_int  in
         let uu____57020 =
           let uu____57022 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____57022  in
         Prims.op_Hat uu____57014 uu____57020  in
       Prims.op_Hat "?" uu____57012)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____57050 = FStar_Syntax_Subst.compress_univ u  in
      match uu____57050 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____57063 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____57074 = FStar_Syntax_Subst.compress_univ u  in
    match uu____57074 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____57085 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____57085
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____57092 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____57092
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____57097 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____57097 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____57118 = univ_to_string u2  in
             let uu____57120 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____57118 uu____57120)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____57126 =
          let uu____57128 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____57128 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____57126
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____57147 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____57147 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____57164 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____57164 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_57182  ->
    match uu___433_57182 with
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
        let uu____57198 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____57198
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____57203 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____57203
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____57216 =
          let uu____57218 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57218  in
        let uu____57219 =
          let uu____57221 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57221 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____57216 uu____57219
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____57247 =
          let uu____57249 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57249  in
        let uu____57250 =
          let uu____57252 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57252 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____57247
          uu____57250
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____57269 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____57269
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
    | uu____57292 ->
        let uu____57295 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____57295 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____57323 ->
        let uu____57326 = quals_to_string quals  in
        Prims.op_Hat uu____57326 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____57522 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____57522
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____57526 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____57526
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____57530 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____57530
    | FStar_Syntax_Syntax.Tm_uinst uu____57533 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____57541 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____57543 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57545,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____57546;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57560,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____57561;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____57575 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____57595 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____57611 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____57619 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____57637 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____57661 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____57689 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____57704 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____57718,m) ->
        let uu____57756 = FStar_ST.op_Bang m  in
        (match uu____57756 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____57814 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____57820,m) ->
        let uu____57826 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____57826
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____57830 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____57833 =
      let uu____57835 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____57835  in
    if uu____57833
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____57849 = FStar_Options.print_implicits ()  in
         if uu____57849 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____57857 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____57882,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____57908,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____57910;
             FStar_Syntax_Syntax.rng = uu____57911;_}
           ->
           let uu____57922 =
             let uu____57924 =
               let uu____57926 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____57926  in
             Prims.op_Hat uu____57924 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____57922
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____57972 =
             let uu____57974 =
               let uu____57976 =
                 let uu____57977 =
                   let uu____57986 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____57986  in
                 uu____57977 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____57976  in
             Prims.op_Hat uu____57974 "]"  in
           Prims.op_Hat "[lazy:" uu____57972
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____58055 =
                  match uu____58055 with
                  | (bv,t) ->
                      let uu____58063 = bv_to_string bv  in
                      let uu____58065 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____58063 uu____58065
                   in
                let uu____58068 = term_to_string tm  in
                let uu____58070 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____58068 uu____58070
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____58079 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____58079)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____58102 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____58139 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____58164  ->
                                 match uu____58164 with
                                 | (t1,uu____58173) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____58139
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____58102 (FStar_String.concat "\\/")  in
           let uu____58188 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____58188
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____58202 = tag_of_term t  in
           let uu____58204 = sli m  in
           let uu____58206 = term_to_string t'  in
           let uu____58208 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____58202
             uu____58204 uu____58206 uu____58208
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____58223 = tag_of_term t  in
           let uu____58225 = term_to_string t'  in
           let uu____58227 = sli m0  in
           let uu____58229 = sli m1  in
           let uu____58231 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____58223 uu____58225 uu____58227 uu____58229 uu____58231
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____58246 = FStar_Range.string_of_range r  in
           let uu____58248 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____58246
             uu____58248
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____58257 = lid_to_string l  in
           let uu____58259 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____58261 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____58257
             uu____58259 uu____58261
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____58265) ->
           let uu____58270 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____58270
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____58274 = db_to_string x3  in
           let uu____58276 =
             let uu____58278 =
               let uu____58280 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____58280 ")"  in
             Prims.op_Hat ":(" uu____58278  in
           Prims.op_Hat uu____58274 uu____58276
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____58287)) ->
           let uu____58302 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58302
           then ctx_uvar_to_string u
           else
             (let uu____58308 =
                let uu____58310 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58310  in
              Prims.op_Hat "?" uu____58308)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____58333 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58333
           then
             let uu____58337 = ctx_uvar_to_string u  in
             let uu____58339 =
               let uu____58341 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____58341 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____58337 uu____58339
           else
             (let uu____58360 =
                let uu____58362 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58362  in
              Prims.op_Hat "?" uu____58360)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____58369 = FStar_Options.print_universes ()  in
           if uu____58369
           then
             let uu____58373 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____58373
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____58401 = binders_to_string " -> " bs  in
           let uu____58404 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____58401 uu____58404
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____58436 = binders_to_string " " bs  in
                let uu____58439 = term_to_string t2  in
                let uu____58441 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____58450 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____58450)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____58436 uu____58439
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____58441
            | uu____58454 ->
                let uu____58457 = binders_to_string " " bs  in
                let uu____58460 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____58457 uu____58460)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____58469 = bv_to_string xt  in
           let uu____58471 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____58474 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____58469 uu____58471
             uu____58474
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____58506 = term_to_string t  in
           let uu____58508 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____58506 uu____58508
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____58531 = lbs_to_string [] lbs  in
           let uu____58533 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____58531 uu____58533
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____58598 =
                   let uu____58600 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____58600
                     (FStar_Util.dflt "default")
                    in
                 let uu____58611 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____58598 uu____58611
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____58632 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____58632
              in
           let uu____58635 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____58635 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____58676 = term_to_string head1  in
           let uu____58678 =
             let uu____58680 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____58713  ->
                       match uu____58713 with
                       | (p,wopt,e) ->
                           let uu____58730 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____58733 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____58738 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____58738
                              in
                           let uu____58742 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____58730
                             uu____58733 uu____58742))
                in
             FStar_Util.concat_l "\n\t|" uu____58680  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____58676
             uu____58678
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____58754 = FStar_Options.print_universes ()  in
           if uu____58754
           then
             let uu____58758 = term_to_string t  in
             let uu____58760 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____58758 uu____58760
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____58767 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____58770 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____58772 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____58767 uu____58770
      uu____58772

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_58775  ->
    match uu___434_58775 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____58781 = FStar_Util.string_of_int i  in
        let uu____58783 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____58781 uu____58783
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____58790 = bv_to_string x  in
        let uu____58792 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____58790 uu____58792
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____58801 = bv_to_string x  in
        let uu____58803 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____58801 uu____58803
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____58810 = FStar_Util.string_of_int i  in
        let uu____58812 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____58810 uu____58812
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____58819 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____58819

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____58823 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____58823 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____58839 =
      let uu____58841 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____58841  in
    if uu____58839
    then
      let e =
        let uu____58846 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____58846  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____58875 = fv_to_string l  in
           let uu____58877 =
             let uu____58879 =
               FStar_List.map
                 (fun uu____58893  ->
                    match uu____58893 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____58879 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____58875 uu____58877
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____58918) ->
           let uu____58923 = FStar_Options.print_bound_var_types ()  in
           if uu____58923
           then
             let uu____58927 = bv_to_string x1  in
             let uu____58929 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____58927 uu____58929
           else
             (let uu____58934 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____58934)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____58938 = FStar_Options.print_bound_var_types ()  in
           if uu____58938
           then
             let uu____58942 = bv_to_string x1  in
             let uu____58944 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____58942 uu____58944
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____58951 = FStar_Options.print_bound_var_types ()  in
           if uu____58951
           then
             let uu____58955 = bv_to_string x1  in
             let uu____58957 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____58955 uu____58957
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____58966 = quals_to_string' quals  in
      let uu____58968 =
        let uu____58970 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____58990 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____58992 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____58994 =
                    let uu____58996 = FStar_Options.print_universes ()  in
                    if uu____58996
                    then
                      let uu____59000 =
                        let uu____59002 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____59002 ">"  in
                      Prims.op_Hat "<" uu____59000
                    else ""  in
                  let uu____59009 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____59011 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____58990
                    uu____58992 uu____58994 uu____59009 uu____59011))
           in
        FStar_Util.concat_l "\n and " uu____58970  in
      FStar_Util.format3 "%slet %s %s" uu____58966
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____58968

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_59026  ->
    match uu___435_59026 with
    | [] -> ""
    | tms ->
        let uu____59034 =
          let uu____59036 =
            FStar_List.map
              (fun t  ->
                 let uu____59044 = term_to_string t  in paren uu____59044)
              tms
             in
          FStar_All.pipe_right uu____59036 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____59034

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____59053 = FStar_Options.print_effect_args ()  in
    if uu____59053
    then
      let uu____59057 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____59057
    else
      (let uu____59060 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____59062 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____59060 uu____59062)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_59066  ->
      match uu___436_59066 with
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
          let uu____59084 =
            let uu____59086 = term_to_string t  in
            Prims.op_Hat uu____59086 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____59084
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
      let uu____59106 =
        let uu____59108 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____59108  in
      if uu____59106
      then
        let uu____59112 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____59112 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____59123 = b  in
         match uu____59123 with
         | (a,imp) ->
             let uu____59137 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____59137
             then
               let uu____59141 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____59141
             else
               (let uu____59146 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____59149 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____59149)
                   in
                if uu____59146
                then
                  let uu____59153 = nm_to_string a  in
                  imp_to_string uu____59153 imp
                else
                  (let uu____59157 =
                     let uu____59159 = nm_to_string a  in
                     let uu____59161 =
                       let uu____59163 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____59163  in
                     Prims.op_Hat uu____59159 uu____59161  in
                   imp_to_string uu____59157 imp)))

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
        let uu____59182 = FStar_Options.print_implicits ()  in
        if uu____59182 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____59193 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____59193 (FStar_String.concat sep)
      else
        (let uu____59221 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____59221 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_59235  ->
    match uu___437_59235 with
    | (a,imp) ->
        let uu____59249 = term_to_string a  in imp_to_string uu____59249 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____59261 = FStar_Options.print_implicits ()  in
      if uu____59261 then args else filter_imp args  in
    let uu____59276 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59276 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____59305 = FStar_Options.ugly ()  in
      if uu____59305
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____59316 =
      let uu____59318 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59318  in
    if uu____59316
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____59339 =
             let uu____59340 = FStar_Syntax_Subst.compress t  in
             uu____59340.FStar_Syntax_Syntax.n  in
           (match uu____59339 with
            | FStar_Syntax_Syntax.Tm_type uu____59344 when
                let uu____59345 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59345 -> term_to_string t
            | uu____59347 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59350 = univ_to_string u  in
                     let uu____59352 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____59350 uu____59352
                 | uu____59355 ->
                     let uu____59358 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____59358))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____59371 =
             let uu____59372 = FStar_Syntax_Subst.compress t  in
             uu____59372.FStar_Syntax_Syntax.n  in
           (match uu____59371 with
            | FStar_Syntax_Syntax.Tm_type uu____59376 when
                let uu____59377 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59377 -> term_to_string t
            | uu____59379 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59382 = univ_to_string u  in
                     let uu____59384 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____59382 uu____59384
                 | uu____59387 ->
                     let uu____59390 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____59390))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____59396 = FStar_Options.print_effect_args ()  in
             if uu____59396
             then
               let uu____59400 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____59402 =
                 let uu____59404 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____59404 (FStar_String.concat ", ")
                  in
               let uu____59419 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____59421 =
                 let uu____59423 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____59423 (FStar_String.concat ", ")
                  in
               let uu____59450 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____59400 uu____59402 uu____59419 uu____59421 uu____59450
             else
               (let uu____59455 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_59461  ->
                           match uu___438_59461 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____59464 -> false)))
                    &&
                    (let uu____59467 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____59467)
                   in
                if uu____59455
                then
                  let uu____59471 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____59471
                else
                  (let uu____59476 =
                     ((let uu____59480 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____59480) &&
                        (let uu____59483 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____59483))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____59476
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____59489 =
                        (let uu____59493 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____59493) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_59499  ->
                                   match uu___439_59499 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____59502 -> false)))
                         in
                      if uu____59489
                      then
                        let uu____59506 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____59506
                      else
                        (let uu____59511 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____59513 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____59511 uu____59513))))
              in
           let dec =
             let uu____59518 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_59531  ->
                       match uu___440_59531 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____59538 =
                             let uu____59540 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____59540
                              in
                           [uu____59538]
                       | uu____59545 -> []))
                in
             FStar_All.pipe_right uu____59518 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____59564 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_59574  ->
    match uu___441_59574 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____59591 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____59628 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____59653  ->
                              match uu____59653 with
                              | (t,uu____59662) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____59628
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____59591 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____59679 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____59679
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____59684) ->
        let uu____59689 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____59689
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____59700 = sli m  in
        let uu____59702 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____59700 uu____59702
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____59712 = sli m  in
        let uu____59714 = sli m'  in
        let uu____59716 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____59712
          uu____59714 uu____59716

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____59731 = FStar_Options.ugly ()  in
      if uu____59731
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
      let uu____59752 = b  in
      match uu____59752 with
      | (a,imp) ->
          let n1 =
            let uu____59760 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____59760
            then FStar_Util.JsonNull
            else
              (let uu____59765 =
                 let uu____59767 = nm_to_string a  in
                 imp_to_string uu____59767 imp  in
               FStar_Util.JsonStr uu____59765)
             in
          let t =
            let uu____59770 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____59770  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____59802 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____59802
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____59820 = FStar_Options.print_universes ()  in
    if uu____59820 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____59836 =
      let uu____59838 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59838  in
    if uu____59836
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____59848 = s  in
       match uu____59848 with
       | (us,t) ->
           let uu____59860 =
             let uu____59862 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____59862  in
           let uu____59866 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____59860 uu____59866)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____59876 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____59878 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____59881 =
      let uu____59883 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____59883  in
    let uu____59887 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____59889 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____59876 uu____59878
      uu____59881 uu____59887 uu____59889
  
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
          let uu____59920 =
            let uu____59922 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____59922  in
          if uu____59920
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____59943 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____59943 (FStar_String.concat ",\n\t")
                in
             let uu____59958 =
               let uu____59962 =
                 let uu____59966 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____59968 =
                   let uu____59972 =
                     let uu____59974 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____59974  in
                   let uu____59978 =
                     let uu____59982 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____59985 =
                       let uu____59989 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____59991 =
                         let uu____59995 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____59997 =
                           let uu____60001 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____60003 =
                             let uu____60007 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____60009 =
                               let uu____60013 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____60015 =
                                 let uu____60019 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____60021 =
                                   let uu____60025 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____60027 =
                                     let uu____60031 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____60033 =
                                       let uu____60037 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____60039 =
                                         let uu____60043 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____60045 =
                                           let uu____60049 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____60051 =
                                             let uu____60055 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____60057 =
                                               let uu____60061 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____60063 =
                                                 let uu____60067 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____60069 =
                                                   let uu____60073 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____60073]  in
                                                 uu____60067 :: uu____60069
                                                  in
                                               uu____60061 :: uu____60063  in
                                             uu____60055 :: uu____60057  in
                                           uu____60049 :: uu____60051  in
                                         uu____60043 :: uu____60045  in
                                       uu____60037 :: uu____60039  in
                                     uu____60031 :: uu____60033  in
                                   uu____60025 :: uu____60027  in
                                 uu____60019 :: uu____60021  in
                               uu____60013 :: uu____60015  in
                             uu____60007 :: uu____60009  in
                           uu____60001 :: uu____60003  in
                         uu____59995 :: uu____59997  in
                       uu____59989 :: uu____59991  in
                     uu____59982 :: uu____59985  in
                   uu____59972 :: uu____59978  in
                 uu____59966 :: uu____59968  in
               (if for_free then "_for_free " else "") :: uu____59962  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____59958)
  
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
          (lid,univs1,tps,k,uu____60147,uu____60148) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____60164 = FStar_Options.print_universes ()  in
          if uu____60164
          then
            let uu____60168 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____60168 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____60177,uu____60178,uu____60179) ->
          let uu____60186 = FStar_Options.print_universes ()  in
          if uu____60186
          then
            let uu____60190 = univ_names_to_string univs1  in
            let uu____60192 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____60190
              lid.FStar_Ident.str uu____60192
          else
            (let uu____60197 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____60197)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____60203 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____60205 =
            let uu____60207 = FStar_Options.print_universes ()  in
            if uu____60207
            then
              let uu____60211 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____60211
            else ""  in
          let uu____60217 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____60203
            lid.FStar_Ident.str uu____60205 uu____60217
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____60223 = FStar_Options.print_universes ()  in
          if uu____60223
          then
            let uu____60227 = univ_names_to_string us  in
            let uu____60229 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____60227 uu____60229
          else
            (let uu____60234 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____60234)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60238) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____60244 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____60244
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____60248) ->
          let uu____60257 =
            let uu____60259 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____60259 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____60257
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____60304) -> lift_wp
            | (uu____60311,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____60319 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____60319 with
           | (us,t) ->
               let uu____60331 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____60333 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____60335 = univ_names_to_string us  in
               let uu____60337 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____60331
                 uu____60333 uu____60335 uu____60337)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____60349 = FStar_Options.print_universes ()  in
          if uu____60349
          then
            let uu____60353 =
              let uu____60358 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____60358  in
            (match uu____60353 with
             | (univs2,t) ->
                 let uu____60372 =
                   let uu____60377 =
                     let uu____60378 = FStar_Syntax_Subst.compress t  in
                     uu____60378.FStar_Syntax_Syntax.n  in
                   match uu____60377 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____60407 -> failwith "impossible"  in
                 (match uu____60372 with
                  | (tps1,c1) ->
                      let uu____60416 = sli l  in
                      let uu____60418 = univ_names_to_string univs2  in
                      let uu____60420 = binders_to_string " " tps1  in
                      let uu____60423 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____60416
                        uu____60418 uu____60420 uu____60423))
          else
            (let uu____60428 = sli l  in
             let uu____60430 = binders_to_string " " tps  in
             let uu____60433 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____60428 uu____60430
               uu____60433)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____60442 =
            let uu____60444 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____60444  in
          let uu____60454 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____60442 uu____60454
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____60458 ->
        let uu____60461 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____60461 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____60478 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____60478 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____60489,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____60491;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____60493;
                        FStar_Syntax_Syntax.lbdef = uu____60494;
                        FStar_Syntax_Syntax.lbattrs = uu____60495;
                        FStar_Syntax_Syntax.lbpos = uu____60496;_}::[]),uu____60497)
        ->
        let uu____60520 = lbname_to_string lb  in
        let uu____60522 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____60520 uu____60522
    | uu____60525 ->
        let uu____60526 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____60526 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____60550 = sli m.FStar_Syntax_Syntax.name  in
    let uu____60552 =
      let uu____60554 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____60554 (FStar_String.concat "\n")  in
    let uu____60564 =
      let uu____60566 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____60566 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____60550
      uu____60552 uu____60564
  
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
          (let uu____60610 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____60610))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____60619 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____60619)));
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
           (let uu____60660 = f x  in
            FStar_Util.string_builder_append strb uu____60660);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____60669 = f x1  in
                 FStar_Util.string_builder_append strb uu____60669)) xs;
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
           (let uu____60716 = f x  in
            FStar_Util.string_builder_append strb uu____60716);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____60725 = f x1  in
                 FStar_Util.string_builder_append strb uu____60725)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____60747 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____60747
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_60760  ->
    match uu___442_60760 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____60776 =
          let uu____60778 =
            let uu____60780 =
              let uu____60782 =
                let uu____60784 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____60784 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____60782 ")"  in
            Prims.op_Hat " " uu____60780  in
          Prims.op_Hat h uu____60778  in
        Prims.op_Hat "(" uu____60776
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____60799 =
          let uu____60801 = emb_typ_to_string a  in
          let uu____60803 =
            let uu____60805 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____60805  in
          Prims.op_Hat uu____60801 uu____60803  in
        Prims.op_Hat "(" uu____60799
  