open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_56079  ->
    match uu___429_56079 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____56083 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____56083
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____56088 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____56088
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____56092 =
          let uu____56094 = delta_depth_to_string d  in
          Prims.op_Hat uu____56094 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____56092
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____56106 = FStar_Options.print_real_names ()  in
    if uu____56106
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56133 =
      let uu____56135 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____56135  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56133
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56145 = FStar_Options.print_real_names ()  in
    if uu____56145
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56158 =
      let uu____56160 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____56160  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56158
  
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
      | uu____56382 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____56395 -> failwith "get_lid"
  
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
  'Auu____56498 'Auu____56499 .
    ('Auu____56498,'Auu____56499) FStar_Util.either -> Prims.bool
  =
  fun uu___430_56509  ->
    match uu___430_56509 with
    | FStar_Util.Inl uu____56514 -> false
    | FStar_Util.Inr uu____56516 -> true
  
let filter_imp :
  'Auu____56523 .
    ('Auu____56523 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____56523 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_56578  ->
            match uu___431_56578 with
            | (uu____56586,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____56593,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____56594)) -> false
            | (uu____56599,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____56600)) -> false
            | uu____56606 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____56624 =
      let uu____56625 = FStar_Syntax_Subst.compress e  in
      uu____56625.FStar_Syntax_Syntax.n  in
    match uu____56624 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____56686 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____56686
        then
          let uu____56695 =
            let uu____56700 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____56700  in
          (match uu____56695 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____56711 =
                 let uu____56714 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____56714 :: xs  in
               FStar_Pervasives_Native.Some uu____56711
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____56726 ->
        let uu____56727 = is_lex_top e  in
        if uu____56727
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____56775 = f hd1  in if uu____56775 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____56807 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____56807
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56838 = get_lid e  in find_lid uu____56838 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56850 = get_lid e  in find_lid uu____56850 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____56862 = get_lid t  in find_lid uu____56862 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_56876  ->
    match uu___432_56876 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____56887 = FStar_Options.hide_uvar_nums ()  in
    if uu____56887
    then "?"
    else
      (let uu____56894 =
         let uu____56896 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____56896 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____56894)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____56908 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____56910 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____56908 uu____56910
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____56936 = FStar_Options.hide_uvar_nums ()  in
    if uu____56936
    then "?"
    else
      (let uu____56943 =
         let uu____56945 =
           let uu____56947 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____56947 FStar_Util.string_of_int  in
         let uu____56951 =
           let uu____56953 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____56953  in
         Prims.op_Hat uu____56945 uu____56951  in
       Prims.op_Hat "?" uu____56943)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____56981 = FStar_Syntax_Subst.compress_univ u  in
      match uu____56981 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____56994 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____57005 = FStar_Syntax_Subst.compress_univ u  in
    match uu____57005 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____57016 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____57016
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____57023 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____57023
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____57028 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____57028 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____57049 = univ_to_string u2  in
             let uu____57051 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____57049 uu____57051)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____57057 =
          let uu____57059 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____57059 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____57057
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____57078 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____57078 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____57095 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____57095 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_57113  ->
    match uu___433_57113 with
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
        let uu____57129 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____57129
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____57134 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____57134
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____57147 =
          let uu____57149 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57149  in
        let uu____57150 =
          let uu____57152 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57152 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____57147 uu____57150
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____57178 =
          let uu____57180 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57180  in
        let uu____57181 =
          let uu____57183 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57183 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____57178
          uu____57181
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____57200 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____57200
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
    | uu____57223 ->
        let uu____57226 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____57226 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____57254 ->
        let uu____57257 = quals_to_string quals  in
        Prims.op_Hat uu____57257 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____57453 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____57453
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____57457 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____57457
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____57461 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____57461
    | FStar_Syntax_Syntax.Tm_uinst uu____57464 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____57472 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____57474 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57476,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____57477;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57491,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____57492;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____57506 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____57526 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____57542 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____57550 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____57568 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____57592 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____57620 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____57635 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____57649,m) ->
        let uu____57687 = FStar_ST.op_Bang m  in
        (match uu____57687 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____57745 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____57751,m) ->
        let uu____57757 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____57757
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____57761 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____57764 =
      let uu____57766 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____57766  in
    if uu____57764
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____57780 = FStar_Options.print_implicits ()  in
         if uu____57780 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____57788 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____57813,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____57839,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____57841;
             FStar_Syntax_Syntax.rng = uu____57842;_}
           ->
           let uu____57853 =
             let uu____57855 =
               let uu____57857 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____57857  in
             Prims.op_Hat uu____57855 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____57853
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____57903 =
             let uu____57905 =
               let uu____57907 =
                 let uu____57908 =
                   let uu____57917 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____57917  in
                 uu____57908 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____57907  in
             Prims.op_Hat uu____57905 "]"  in
           Prims.op_Hat "[lazy:" uu____57903
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____57986 =
                  match uu____57986 with
                  | (bv,t) ->
                      let uu____57994 = bv_to_string bv  in
                      let uu____57996 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____57994 uu____57996
                   in
                let uu____57999 = term_to_string tm  in
                let uu____58001 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____57999 uu____58001
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____58010 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____58010)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____58033 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____58070 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____58095  ->
                                 match uu____58095 with
                                 | (t1,uu____58104) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____58070
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____58033 (FStar_String.concat "\\/")  in
           let uu____58119 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____58119
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____58133 = tag_of_term t  in
           let uu____58135 = sli m  in
           let uu____58137 = term_to_string t'  in
           let uu____58139 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____58133
             uu____58135 uu____58137 uu____58139
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____58154 = tag_of_term t  in
           let uu____58156 = term_to_string t'  in
           let uu____58158 = sli m0  in
           let uu____58160 = sli m1  in
           let uu____58162 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____58154 uu____58156 uu____58158 uu____58160 uu____58162
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____58177 = FStar_Range.string_of_range r  in
           let uu____58179 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____58177
             uu____58179
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____58188 = lid_to_string l  in
           let uu____58190 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____58192 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____58188
             uu____58190 uu____58192
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____58196) ->
           let uu____58201 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____58201
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____58205 = db_to_string x3  in
           let uu____58207 =
             let uu____58209 =
               let uu____58211 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____58211 ")"  in
             Prims.op_Hat ":(" uu____58209  in
           Prims.op_Hat uu____58205 uu____58207
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____58218)) ->
           let uu____58233 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58233
           then ctx_uvar_to_string u
           else
             (let uu____58239 =
                let uu____58241 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58241  in
              Prims.op_Hat "?" uu____58239)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____58264 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58264
           then
             let uu____58268 = ctx_uvar_to_string u  in
             let uu____58270 =
               let uu____58272 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____58272 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____58268 uu____58270
           else
             (let uu____58291 =
                let uu____58293 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58293  in
              Prims.op_Hat "?" uu____58291)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____58300 = FStar_Options.print_universes ()  in
           if uu____58300
           then
             let uu____58304 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____58304
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____58332 = binders_to_string " -> " bs  in
           let uu____58335 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____58332 uu____58335
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____58367 = binders_to_string " " bs  in
                let uu____58370 = term_to_string t2  in
                let uu____58372 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____58381 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____58381)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____58367 uu____58370
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____58372
            | uu____58385 ->
                let uu____58388 = binders_to_string " " bs  in
                let uu____58391 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____58388 uu____58391)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____58400 = bv_to_string xt  in
           let uu____58402 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____58405 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____58400 uu____58402
             uu____58405
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____58437 = term_to_string t  in
           let uu____58439 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____58437 uu____58439
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____58462 = lbs_to_string [] lbs  in
           let uu____58464 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____58462 uu____58464
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____58529 =
                   let uu____58531 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____58531
                     (FStar_Util.dflt "default")
                    in
                 let uu____58542 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____58529 uu____58542
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____58563 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____58563
              in
           let uu____58566 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____58566 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____58607 = term_to_string head1  in
           let uu____58609 =
             let uu____58611 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____58644  ->
                       match uu____58644 with
                       | (p,wopt,e) ->
                           let uu____58661 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____58664 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____58669 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____58669
                              in
                           let uu____58673 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____58661
                             uu____58664 uu____58673))
                in
             FStar_Util.concat_l "\n\t|" uu____58611  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____58607
             uu____58609
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____58685 = FStar_Options.print_universes ()  in
           if uu____58685
           then
             let uu____58689 = term_to_string t  in
             let uu____58691 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____58689 uu____58691
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____58698 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____58701 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____58703 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____58698 uu____58701
      uu____58703

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_58706  ->
    match uu___434_58706 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____58712 = FStar_Util.string_of_int i  in
        let uu____58714 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____58712 uu____58714
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____58721 = bv_to_string x  in
        let uu____58723 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____58721 uu____58723
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____58732 = bv_to_string x  in
        let uu____58734 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____58732 uu____58734
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____58741 = FStar_Util.string_of_int i  in
        let uu____58743 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____58741 uu____58743
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____58750 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____58750

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____58754 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____58754 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____58770 =
      let uu____58772 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____58772  in
    if uu____58770
    then
      let e =
        let uu____58777 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____58777  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____58806 = fv_to_string l  in
           let uu____58808 =
             let uu____58810 =
               FStar_List.map
                 (fun uu____58824  ->
                    match uu____58824 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____58810 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____58806 uu____58808
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____58849) ->
           let uu____58854 = FStar_Options.print_bound_var_types ()  in
           if uu____58854
           then
             let uu____58858 = bv_to_string x1  in
             let uu____58860 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____58858 uu____58860
           else
             (let uu____58865 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____58865)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____58869 = FStar_Options.print_bound_var_types ()  in
           if uu____58869
           then
             let uu____58873 = bv_to_string x1  in
             let uu____58875 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____58873 uu____58875
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____58882 = FStar_Options.print_bound_var_types ()  in
           if uu____58882
           then
             let uu____58886 = bv_to_string x1  in
             let uu____58888 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____58886 uu____58888
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____58897 = quals_to_string' quals  in
      let uu____58899 =
        let uu____58901 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____58921 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____58923 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____58925 =
                    let uu____58927 = FStar_Options.print_universes ()  in
                    if uu____58927
                    then
                      let uu____58931 =
                        let uu____58933 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____58933 ">"  in
                      Prims.op_Hat "<" uu____58931
                    else ""  in
                  let uu____58940 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____58942 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____58921
                    uu____58923 uu____58925 uu____58940 uu____58942))
           in
        FStar_Util.concat_l "\n and " uu____58901  in
      FStar_Util.format3 "%slet %s %s" uu____58897
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____58899

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_58957  ->
    match uu___435_58957 with
    | [] -> ""
    | tms ->
        let uu____58965 =
          let uu____58967 =
            FStar_List.map
              (fun t  ->
                 let uu____58975 = term_to_string t  in paren uu____58975)
              tms
             in
          FStar_All.pipe_right uu____58967 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____58965

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____58984 = FStar_Options.print_effect_args ()  in
    if uu____58984
    then
      let uu____58988 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____58988
    else
      (let uu____58991 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____58993 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____58991 uu____58993)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_58997  ->
      match uu___436_58997 with
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
          let uu____59015 =
            let uu____59017 = term_to_string t  in
            Prims.op_Hat uu____59017 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____59015
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
      let uu____59037 =
        let uu____59039 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____59039  in
      if uu____59037
      then
        let uu____59043 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____59043 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____59054 = b  in
         match uu____59054 with
         | (a,imp) ->
             let uu____59068 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____59068
             then
               let uu____59072 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____59072
             else
               (let uu____59077 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____59080 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____59080)
                   in
                if uu____59077
                then
                  let uu____59084 = nm_to_string a  in
                  imp_to_string uu____59084 imp
                else
                  (let uu____59088 =
                     let uu____59090 = nm_to_string a  in
                     let uu____59092 =
                       let uu____59094 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____59094  in
                     Prims.op_Hat uu____59090 uu____59092  in
                   imp_to_string uu____59088 imp)))

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
        let uu____59113 = FStar_Options.print_implicits ()  in
        if uu____59113 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____59124 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____59124 (FStar_String.concat sep)
      else
        (let uu____59152 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____59152 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_59166  ->
    match uu___437_59166 with
    | (a,imp) ->
        let uu____59180 = term_to_string a  in imp_to_string uu____59180 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____59192 = FStar_Options.print_implicits ()  in
      if uu____59192 then args else filter_imp args  in
    let uu____59207 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59207 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____59236 = FStar_Options.ugly ()  in
      if uu____59236
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____59247 =
      let uu____59249 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59249  in
    if uu____59247
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____59270 =
             let uu____59271 = FStar_Syntax_Subst.compress t  in
             uu____59271.FStar_Syntax_Syntax.n  in
           (match uu____59270 with
            | FStar_Syntax_Syntax.Tm_type uu____59275 when
                let uu____59276 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59276 -> term_to_string t
            | uu____59278 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59281 = univ_to_string u  in
                     let uu____59283 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____59281 uu____59283
                 | uu____59286 ->
                     let uu____59289 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____59289))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____59302 =
             let uu____59303 = FStar_Syntax_Subst.compress t  in
             uu____59303.FStar_Syntax_Syntax.n  in
           (match uu____59302 with
            | FStar_Syntax_Syntax.Tm_type uu____59307 when
                let uu____59308 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59308 -> term_to_string t
            | uu____59310 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59313 = univ_to_string u  in
                     let uu____59315 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____59313 uu____59315
                 | uu____59318 ->
                     let uu____59321 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____59321))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____59327 = FStar_Options.print_effect_args ()  in
             if uu____59327
             then
               let uu____59331 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____59333 =
                 let uu____59335 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____59335 (FStar_String.concat ", ")
                  in
               let uu____59350 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____59352 =
                 let uu____59354 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____59354 (FStar_String.concat ", ")
                  in
               let uu____59381 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____59331 uu____59333 uu____59350 uu____59352 uu____59381
             else
               (let uu____59386 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_59392  ->
                           match uu___438_59392 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____59395 -> false)))
                    &&
                    (let uu____59398 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____59398)
                   in
                if uu____59386
                then
                  let uu____59402 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____59402
                else
                  (let uu____59407 =
                     ((let uu____59411 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____59411) &&
                        (let uu____59414 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____59414))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____59407
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____59420 =
                        (let uu____59424 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____59424) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_59430  ->
                                   match uu___439_59430 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____59433 -> false)))
                         in
                      if uu____59420
                      then
                        let uu____59437 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____59437
                      else
                        (let uu____59442 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____59444 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____59442 uu____59444))))
              in
           let dec =
             let uu____59449 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_59462  ->
                       match uu___440_59462 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____59469 =
                             let uu____59471 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____59471
                              in
                           [uu____59469]
                       | uu____59476 -> []))
                in
             FStar_All.pipe_right uu____59449 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____59495 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_59505  ->
    match uu___441_59505 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____59522 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____59559 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____59584  ->
                              match uu____59584 with
                              | (t,uu____59593) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____59559
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____59522 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____59610 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____59610
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____59615) ->
        let uu____59620 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____59620
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____59631 = sli m  in
        let uu____59633 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____59631 uu____59633
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____59643 = sli m  in
        let uu____59645 = sli m'  in
        let uu____59647 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____59643
          uu____59645 uu____59647

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____59662 = FStar_Options.ugly ()  in
      if uu____59662
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
      let uu____59683 = b  in
      match uu____59683 with
      | (a,imp) ->
          let n1 =
            let uu____59691 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____59691
            then FStar_Util.JsonNull
            else
              (let uu____59696 =
                 let uu____59698 = nm_to_string a  in
                 imp_to_string uu____59698 imp  in
               FStar_Util.JsonStr uu____59696)
             in
          let t =
            let uu____59701 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____59701  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____59733 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____59733
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____59751 = FStar_Options.print_universes ()  in
    if uu____59751 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____59767 =
      let uu____59769 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59769  in
    if uu____59767
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____59779 = s  in
       match uu____59779 with
       | (us,t) ->
           let uu____59791 =
             let uu____59793 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____59793  in
           let uu____59797 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____59791 uu____59797)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____59807 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____59809 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____59812 =
      let uu____59814 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____59814  in
    let uu____59818 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____59820 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____59807 uu____59809
      uu____59812 uu____59818 uu____59820
  
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
          let uu____59851 =
            let uu____59853 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____59853  in
          if uu____59851
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____59874 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____59874 (FStar_String.concat ",\n\t")
                in
             let uu____59889 =
               let uu____59893 =
                 let uu____59897 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____59899 =
                   let uu____59903 =
                     let uu____59905 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____59905  in
                   let uu____59909 =
                     let uu____59913 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____59916 =
                       let uu____59920 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____59922 =
                         let uu____59926 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____59928 =
                           let uu____59932 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____59934 =
                             let uu____59938 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____59940 =
                               let uu____59944 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____59946 =
                                 let uu____59950 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____59952 =
                                   let uu____59956 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____59958 =
                                     let uu____59962 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____59964 =
                                       let uu____59968 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____59970 =
                                         let uu____59974 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____59976 =
                                           let uu____59980 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____59982 =
                                             let uu____59986 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____59988 =
                                               let uu____59992 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____59994 =
                                                 let uu____59998 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____60000 =
                                                   let uu____60004 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____60004]  in
                                                 uu____59998 :: uu____60000
                                                  in
                                               uu____59992 :: uu____59994  in
                                             uu____59986 :: uu____59988  in
                                           uu____59980 :: uu____59982  in
                                         uu____59974 :: uu____59976  in
                                       uu____59968 :: uu____59970  in
                                     uu____59962 :: uu____59964  in
                                   uu____59956 :: uu____59958  in
                                 uu____59950 :: uu____59952  in
                               uu____59944 :: uu____59946  in
                             uu____59938 :: uu____59940  in
                           uu____59932 :: uu____59934  in
                         uu____59926 :: uu____59928  in
                       uu____59920 :: uu____59922  in
                     uu____59913 :: uu____59916  in
                   uu____59903 :: uu____59909  in
                 uu____59897 :: uu____59899  in
               (if for_free then "_for_free " else "") :: uu____59893  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____59889)
  
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
          (lid,univs1,tps,k,uu____60078,uu____60079) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____60095 = FStar_Options.print_universes ()  in
          if uu____60095
          then
            let uu____60099 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____60099 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____60108,uu____60109,uu____60110) ->
          let uu____60117 = FStar_Options.print_universes ()  in
          if uu____60117
          then
            let uu____60121 = univ_names_to_string univs1  in
            let uu____60123 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____60121
              lid.FStar_Ident.str uu____60123
          else
            (let uu____60128 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____60128)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____60134 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____60136 =
            let uu____60138 = FStar_Options.print_universes ()  in
            if uu____60138
            then
              let uu____60142 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____60142
            else ""  in
          let uu____60148 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____60134
            lid.FStar_Ident.str uu____60136 uu____60148
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____60154 = FStar_Options.print_universes ()  in
          if uu____60154
          then
            let uu____60158 = univ_names_to_string us  in
            let uu____60160 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____60158 uu____60160
          else
            (let uu____60165 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____60165)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60169) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____60175 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____60175
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____60179) ->
          let uu____60188 =
            let uu____60190 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____60190 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____60188
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____60235) -> lift_wp
            | (uu____60242,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____60250 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____60250 with
           | (us,t) ->
               let uu____60262 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____60264 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____60266 = univ_names_to_string us  in
               let uu____60268 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____60262
                 uu____60264 uu____60266 uu____60268)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____60280 = FStar_Options.print_universes ()  in
          if uu____60280
          then
            let uu____60284 =
              let uu____60289 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____60289  in
            (match uu____60284 with
             | (univs2,t) ->
                 let uu____60303 =
                   let uu____60308 =
                     let uu____60309 = FStar_Syntax_Subst.compress t  in
                     uu____60309.FStar_Syntax_Syntax.n  in
                   match uu____60308 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____60338 -> failwith "impossible"  in
                 (match uu____60303 with
                  | (tps1,c1) ->
                      let uu____60347 = sli l  in
                      let uu____60349 = univ_names_to_string univs2  in
                      let uu____60351 = binders_to_string " " tps1  in
                      let uu____60354 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____60347
                        uu____60349 uu____60351 uu____60354))
          else
            (let uu____60359 = sli l  in
             let uu____60361 = binders_to_string " " tps  in
             let uu____60364 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____60359 uu____60361
               uu____60364)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____60373 =
            let uu____60375 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____60375  in
          let uu____60385 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____60373 uu____60385
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____60389 ->
        let uu____60392 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____60392 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____60409 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____60409 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____60420,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____60422;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____60424;
                        FStar_Syntax_Syntax.lbdef = uu____60425;
                        FStar_Syntax_Syntax.lbattrs = uu____60426;
                        FStar_Syntax_Syntax.lbpos = uu____60427;_}::[]),uu____60428)
        ->
        let uu____60451 = lbname_to_string lb  in
        let uu____60453 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____60451 uu____60453
    | uu____60456 ->
        let uu____60457 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____60457 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____60481 = sli m.FStar_Syntax_Syntax.name  in
    let uu____60483 =
      let uu____60485 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____60485 (FStar_String.concat "\n")  in
    let uu____60495 =
      let uu____60497 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____60497 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____60481
      uu____60483 uu____60495
  
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
          (let uu____60541 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____60541))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____60550 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____60550)));
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
           (let uu____60591 = f x  in
            FStar_Util.string_builder_append strb uu____60591);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____60600 = f x1  in
                 FStar_Util.string_builder_append strb uu____60600)) xs;
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
           (let uu____60647 = f x  in
            FStar_Util.string_builder_append strb uu____60647);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____60656 = f x1  in
                 FStar_Util.string_builder_append strb uu____60656)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____60678 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____60678
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_60691  ->
    match uu___442_60691 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____60707 =
          let uu____60709 =
            let uu____60711 =
              let uu____60713 =
                let uu____60715 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____60715 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____60713 ")"  in
            Prims.op_Hat " " uu____60711  in
          Prims.op_Hat h uu____60709  in
        Prims.op_Hat "(" uu____60707
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____60730 =
          let uu____60732 = emb_typ_to_string a  in
          let uu____60734 =
            let uu____60736 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____60736  in
          Prims.op_Hat uu____60732 uu____60734  in
        Prims.op_Hat "(" uu____60730
  