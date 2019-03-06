open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_52248  ->
    match uu___429_52248 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____52252 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____52252
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____52257 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____52257
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____52261 =
          let uu____52263 = delta_depth_to_string d  in
          Prims.op_Hat uu____52263 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____52261
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____52275 = FStar_Options.print_real_names ()  in
    if uu____52275
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____52302 =
      let uu____52304 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____52304  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____52302
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____52314 = FStar_Options.print_real_names ()  in
    if uu____52314
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____52327 =
      let uu____52329 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____52329  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____52327
  
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
      | uu____52551 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____52564 -> failwith "get_lid"
  
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
  'Auu____52667 'Auu____52668 .
    ('Auu____52667,'Auu____52668) FStar_Util.either -> Prims.bool
  =
  fun uu___430_52678  ->
    match uu___430_52678 with
    | FStar_Util.Inl uu____52683 -> false
    | FStar_Util.Inr uu____52685 -> true
  
let filter_imp :
  'Auu____52692 .
    ('Auu____52692 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____52692 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_52747  ->
            match uu___431_52747 with
            | (uu____52755,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____52762,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____52763)) -> false
            | (uu____52768,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____52769)) -> false
            | uu____52775 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____52793 =
      let uu____52794 = FStar_Syntax_Subst.compress e  in
      uu____52794.FStar_Syntax_Syntax.n  in
    match uu____52793 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____52855 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____52855
        then
          let uu____52864 =
            let uu____52869 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____52869  in
          (match uu____52864 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____52880 =
                 let uu____52883 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____52883 :: xs  in
               FStar_Pervasives_Native.Some uu____52880
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____52895 ->
        let uu____52896 = is_lex_top e  in
        if uu____52896
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____52944 = f hd1  in if uu____52944 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____52976 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____52976
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____53007 = get_lid e  in find_lid uu____53007 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____53019 = get_lid e  in find_lid uu____53019 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____53031 = get_lid t  in find_lid uu____53031 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_53045  ->
    match uu___432_53045 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____53056 = FStar_Options.hide_uvar_nums ()  in
    if uu____53056
    then "?"
    else
      (let uu____53063 =
         let uu____53065 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____53065 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____53063)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____53077 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____53079 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____53077 uu____53079
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____53105 = FStar_Options.hide_uvar_nums ()  in
    if uu____53105
    then "?"
    else
      (let uu____53112 =
         let uu____53114 =
           let uu____53116 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____53116 FStar_Util.string_of_int  in
         let uu____53120 =
           let uu____53122 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____53122  in
         Prims.op_Hat uu____53114 uu____53120  in
       Prims.op_Hat "?" uu____53112)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____53150 = FStar_Syntax_Subst.compress_univ u  in
      match uu____53150 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____53163 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____53174 = FStar_Syntax_Subst.compress_univ u  in
    match uu____53174 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____53185 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____53185
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____53192 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____53192
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____53197 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____53197 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____53218 = univ_to_string u2  in
             let uu____53220 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____53218 uu____53220)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____53226 =
          let uu____53228 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____53228 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____53226
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____53247 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____53247 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____53264 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____53264 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_53282  ->
    match uu___433_53282 with
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
        let uu____53298 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____53298
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____53303 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____53303
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____53316 =
          let uu____53318 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____53318  in
        let uu____53319 =
          let uu____53321 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____53321 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____53316 uu____53319
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____53347 =
          let uu____53349 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____53349  in
        let uu____53350 =
          let uu____53352 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____53352 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____53347
          uu____53350
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____53369 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____53369
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
    | uu____53392 ->
        let uu____53395 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____53395 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____53423 ->
        let uu____53426 = quals_to_string quals  in
        Prims.op_Hat uu____53426 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____53622 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____53622
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____53626 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____53626
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____53630 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____53630
    | FStar_Syntax_Syntax.Tm_uinst uu____53633 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____53641 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____53643 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____53645,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____53646;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____53660,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____53661;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____53675 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____53695 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____53711 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____53719 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____53737 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____53761 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____53789 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____53804 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____53818,m) ->
        let uu____53856 = FStar_ST.op_Bang m  in
        (match uu____53856 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____53892 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____53898,m) ->
        let uu____53904 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____53904
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____53908 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____53911 =
      let uu____53913 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____53913  in
    if uu____53911
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____53927 = FStar_Options.print_implicits ()  in
         if uu____53927 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____53935 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____53960,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____53986,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____53988;
             FStar_Syntax_Syntax.rng = uu____53989;_}
           ->
           let uu____54000 =
             let uu____54002 =
               let uu____54004 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____54004  in
             Prims.op_Hat uu____54002 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____54000
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____54010 =
             let uu____54012 =
               let uu____54014 =
                 let uu____54015 =
                   let uu____54024 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____54024  in
                 uu____54015 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____54014  in
             Prims.op_Hat uu____54012 "]"  in
           Prims.op_Hat "[lazy:" uu____54010
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____54093 =
                  match uu____54093 with
                  | (bv,t) ->
                      let uu____54101 = bv_to_string bv  in
                      let uu____54103 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____54101 uu____54103
                   in
                let uu____54106 = term_to_string tm  in
                let uu____54108 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____54106 uu____54108
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____54117 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____54117)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____54140 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____54177 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____54202  ->
                                 match uu____54202 with
                                 | (t1,uu____54211) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____54177
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____54140 (FStar_String.concat "\\/")  in
           let uu____54226 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____54226
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____54240 = tag_of_term t  in
           let uu____54242 = sli m  in
           let uu____54244 = term_to_string t'  in
           let uu____54246 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____54240
             uu____54242 uu____54244 uu____54246
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____54261 = tag_of_term t  in
           let uu____54263 = term_to_string t'  in
           let uu____54265 = sli m0  in
           let uu____54267 = sli m1  in
           let uu____54269 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____54261 uu____54263 uu____54265 uu____54267 uu____54269
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____54284 = FStar_Range.string_of_range r  in
           let uu____54286 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____54284
             uu____54286
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____54295 = lid_to_string l  in
           let uu____54297 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____54299 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____54295
             uu____54297 uu____54299
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____54303) ->
           let uu____54308 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____54308
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____54312 = db_to_string x3  in
           let uu____54314 =
             let uu____54316 =
               let uu____54318 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____54318 ")"  in
             Prims.op_Hat ":(" uu____54316  in
           Prims.op_Hat uu____54312 uu____54314
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____54325)) ->
           let uu____54340 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____54340
           then ctx_uvar_to_string u
           else
             (let uu____54346 =
                let uu____54348 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____54348  in
              Prims.op_Hat "?" uu____54346)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____54371 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____54371
           then
             let uu____54375 = ctx_uvar_to_string u  in
             let uu____54377 =
               let uu____54379 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____54379 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____54375 uu____54377
           else
             (let uu____54398 =
                let uu____54400 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____54400  in
              Prims.op_Hat "?" uu____54398)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____54407 = FStar_Options.print_universes ()  in
           if uu____54407
           then
             let uu____54411 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____54411
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____54439 = binders_to_string " -> " bs  in
           let uu____54442 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____54439 uu____54442
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____54474 = binders_to_string " " bs  in
                let uu____54477 = term_to_string t2  in
                let uu____54479 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____54488 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____54488)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____54474 uu____54477
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____54479
            | uu____54492 ->
                let uu____54495 = binders_to_string " " bs  in
                let uu____54498 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____54495 uu____54498)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____54507 = bv_to_string xt  in
           let uu____54509 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____54512 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____54507 uu____54509
             uu____54512
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____54544 = term_to_string t  in
           let uu____54546 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____54544 uu____54546
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____54569 = lbs_to_string [] lbs  in
           let uu____54571 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____54569 uu____54571
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____54636 =
                   let uu____54638 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____54638
                     (FStar_Util.dflt "default")
                    in
                 let uu____54649 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____54636 uu____54649
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____54670 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____54670
              in
           let uu____54673 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____54673 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____54714 = term_to_string head1  in
           let uu____54716 =
             let uu____54718 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____54751  ->
                       match uu____54751 with
                       | (p,wopt,e) ->
                           let uu____54768 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____54771 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____54776 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____54776
                              in
                           let uu____54780 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____54768
                             uu____54771 uu____54780))
                in
             FStar_Util.concat_l "\n\t|" uu____54718  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____54714
             uu____54716
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____54792 = FStar_Options.print_universes ()  in
           if uu____54792
           then
             let uu____54796 = term_to_string t  in
             let uu____54798 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____54796 uu____54798
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____54805 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____54808 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____54810 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____54805 uu____54808
      uu____54810

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_54813  ->
    match uu___434_54813 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____54819 = FStar_Util.string_of_int i  in
        let uu____54821 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____54819 uu____54821
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____54828 = bv_to_string x  in
        let uu____54830 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____54828 uu____54830
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____54839 = bv_to_string x  in
        let uu____54841 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____54839 uu____54841
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____54848 = FStar_Util.string_of_int i  in
        let uu____54850 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____54848 uu____54850
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____54857 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____54857

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____54861 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____54861 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____54877 =
      let uu____54879 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54879  in
    if uu____54877
    then
      let e =
        let uu____54884 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____54884  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____54913 = fv_to_string l  in
           let uu____54915 =
             let uu____54917 =
               FStar_List.map
                 (fun uu____54931  ->
                    match uu____54931 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____54917 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____54913 uu____54915
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____54956) ->
           let uu____54961 = FStar_Options.print_bound_var_types ()  in
           if uu____54961
           then
             let uu____54965 = bv_to_string x1  in
             let uu____54967 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____54965 uu____54967
           else
             (let uu____54972 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____54972)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____54976 = FStar_Options.print_bound_var_types ()  in
           if uu____54976
           then
             let uu____54980 = bv_to_string x1  in
             let uu____54982 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____54980 uu____54982
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____54989 = FStar_Options.print_bound_var_types ()  in
           if uu____54989
           then
             let uu____54993 = bv_to_string x1  in
             let uu____54995 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____54993 uu____54995
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____55004 = quals_to_string' quals  in
      let uu____55006 =
        let uu____55008 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____55028 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____55030 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____55032 =
                    let uu____55034 = FStar_Options.print_universes ()  in
                    if uu____55034
                    then
                      let uu____55038 =
                        let uu____55040 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____55040 ">"  in
                      Prims.op_Hat "<" uu____55038
                    else ""  in
                  let uu____55047 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____55049 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____55028
                    uu____55030 uu____55032 uu____55047 uu____55049))
           in
        FStar_Util.concat_l "\n and " uu____55008  in
      FStar_Util.format3 "%slet %s %s" uu____55004
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____55006

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_55064  ->
    match uu___435_55064 with
    | [] -> ""
    | tms ->
        let uu____55072 =
          let uu____55074 =
            FStar_List.map
              (fun t  ->
                 let uu____55082 = term_to_string t  in paren uu____55082)
              tms
             in
          FStar_All.pipe_right uu____55074 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____55072

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____55091 = FStar_Options.print_effect_args ()  in
    if uu____55091
    then
      let uu____55095 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____55095
    else
      (let uu____55098 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____55100 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____55098 uu____55100)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_55104  ->
      match uu___436_55104 with
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
          let uu____55122 =
            let uu____55124 = term_to_string t  in
            Prims.op_Hat uu____55124 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____55122
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
      let uu____55144 =
        let uu____55146 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____55146  in
      if uu____55144
      then
        let uu____55150 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____55150 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____55161 = b  in
         match uu____55161 with
         | (a,imp) ->
             let uu____55175 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____55175
             then
               let uu____55179 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____55179
             else
               (let uu____55184 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____55187 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____55187)
                   in
                if uu____55184
                then
                  let uu____55191 = nm_to_string a  in
                  imp_to_string uu____55191 imp
                else
                  (let uu____55195 =
                     let uu____55197 = nm_to_string a  in
                     let uu____55199 =
                       let uu____55201 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____55201  in
                     Prims.op_Hat uu____55197 uu____55199  in
                   imp_to_string uu____55195 imp)))

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
        let uu____55220 = FStar_Options.print_implicits ()  in
        if uu____55220 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____55231 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____55231 (FStar_String.concat sep)
      else
        (let uu____55259 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____55259 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_55273  ->
    match uu___437_55273 with
    | (a,imp) ->
        let uu____55287 = term_to_string a  in imp_to_string uu____55287 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____55299 = FStar_Options.print_implicits ()  in
      if uu____55299 then args else filter_imp args  in
    let uu____55314 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____55314 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____55343 = FStar_Options.ugly ()  in
      if uu____55343
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____55354 =
      let uu____55356 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____55356  in
    if uu____55354
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____55377 =
             let uu____55378 = FStar_Syntax_Subst.compress t  in
             uu____55378.FStar_Syntax_Syntax.n  in
           (match uu____55377 with
            | FStar_Syntax_Syntax.Tm_type uu____55382 when
                let uu____55383 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____55383 -> term_to_string t
            | uu____55385 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____55388 = univ_to_string u  in
                     let uu____55390 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____55388 uu____55390
                 | uu____55393 ->
                     let uu____55396 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____55396))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____55409 =
             let uu____55410 = FStar_Syntax_Subst.compress t  in
             uu____55410.FStar_Syntax_Syntax.n  in
           (match uu____55409 with
            | FStar_Syntax_Syntax.Tm_type uu____55414 when
                let uu____55415 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____55415 -> term_to_string t
            | uu____55417 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____55420 = univ_to_string u  in
                     let uu____55422 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____55420 uu____55422
                 | uu____55425 ->
                     let uu____55428 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____55428))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____55434 = FStar_Options.print_effect_args ()  in
             if uu____55434
             then
               let uu____55438 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____55440 =
                 let uu____55442 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____55442 (FStar_String.concat ", ")
                  in
               let uu____55457 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____55459 =
                 let uu____55461 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____55461 (FStar_String.concat ", ")
                  in
               let uu____55488 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____55438 uu____55440 uu____55457 uu____55459 uu____55488
             else
               (let uu____55493 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_55499  ->
                           match uu___438_55499 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____55502 -> false)))
                    &&
                    (let uu____55505 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____55505)
                   in
                if uu____55493
                then
                  let uu____55509 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____55509
                else
                  (let uu____55514 =
                     ((let uu____55518 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____55518) &&
                        (let uu____55521 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____55521))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____55514
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____55527 =
                        (let uu____55531 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____55531) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_55537  ->
                                   match uu___439_55537 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____55540 -> false)))
                         in
                      if uu____55527
                      then
                        let uu____55544 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____55544
                      else
                        (let uu____55549 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____55551 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____55549 uu____55551))))
              in
           let dec =
             let uu____55556 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_55569  ->
                       match uu___440_55569 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____55576 =
                             let uu____55578 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____55578
                              in
                           [uu____55576]
                       | uu____55583 -> []))
                in
             FStar_All.pipe_right uu____55556 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____55602 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_55612  ->
    match uu___441_55612 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____55629 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____55666 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____55691  ->
                              match uu____55691 with
                              | (t,uu____55700) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____55666
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____55629 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____55717 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____55717
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____55722) ->
        let uu____55727 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____55727
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____55738 = sli m  in
        let uu____55740 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____55738 uu____55740
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____55750 = sli m  in
        let uu____55752 = sli m'  in
        let uu____55754 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____55750
          uu____55752 uu____55754

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____55769 = FStar_Options.ugly ()  in
      if uu____55769
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
      let uu____55790 = b  in
      match uu____55790 with
      | (a,imp) ->
          let n1 =
            let uu____55798 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____55798
            then FStar_Util.JsonNull
            else
              (let uu____55803 =
                 let uu____55805 = nm_to_string a  in
                 imp_to_string uu____55805 imp  in
               FStar_Util.JsonStr uu____55803)
             in
          let t =
            let uu____55808 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____55808  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____55840 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____55840
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____55858 = FStar_Options.print_universes ()  in
    if uu____55858 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____55874 =
      let uu____55876 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____55876  in
    if uu____55874
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____55886 = s  in
       match uu____55886 with
       | (us,t) ->
           let uu____55898 =
             let uu____55900 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____55900  in
           let uu____55904 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____55898 uu____55904)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____55914 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____55916 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____55919 =
      let uu____55921 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____55921  in
    let uu____55925 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____55927 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____55914 uu____55916
      uu____55919 uu____55925 uu____55927
  
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
          let uu____55958 =
            let uu____55960 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____55960  in
          if uu____55958
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____55981 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____55981 (FStar_String.concat ",\n\t")
                in
             let uu____55996 =
               let uu____56000 =
                 let uu____56004 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____56006 =
                   let uu____56010 =
                     let uu____56012 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____56012  in
                   let uu____56016 =
                     let uu____56020 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____56023 =
                       let uu____56027 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____56029 =
                         let uu____56033 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____56035 =
                           let uu____56039 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____56041 =
                             let uu____56045 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____56047 =
                               let uu____56051 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____56053 =
                                 let uu____56057 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____56059 =
                                   let uu____56063 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____56065 =
                                     let uu____56069 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____56071 =
                                       let uu____56075 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____56077 =
                                         let uu____56081 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____56083 =
                                           let uu____56087 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____56089 =
                                             let uu____56093 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____56095 =
                                               let uu____56099 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____56101 =
                                                 let uu____56105 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____56107 =
                                                   let uu____56111 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____56111]  in
                                                 uu____56105 :: uu____56107
                                                  in
                                               uu____56099 :: uu____56101  in
                                             uu____56093 :: uu____56095  in
                                           uu____56087 :: uu____56089  in
                                         uu____56081 :: uu____56083  in
                                       uu____56075 :: uu____56077  in
                                     uu____56069 :: uu____56071  in
                                   uu____56063 :: uu____56065  in
                                 uu____56057 :: uu____56059  in
                               uu____56051 :: uu____56053  in
                             uu____56045 :: uu____56047  in
                           uu____56039 :: uu____56041  in
                         uu____56033 :: uu____56035  in
                       uu____56027 :: uu____56029  in
                     uu____56020 :: uu____56023  in
                   uu____56010 :: uu____56016  in
                 uu____56004 :: uu____56006  in
               (if for_free then "_for_free " else "") :: uu____56000  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____55996)
  
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
          (lid,univs1,tps,k,uu____56185,uu____56186) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____56202 = FStar_Options.print_universes ()  in
          if uu____56202
          then
            let uu____56206 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____56206 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____56215,uu____56216,uu____56217) ->
          let uu____56224 = FStar_Options.print_universes ()  in
          if uu____56224
          then
            let uu____56228 = univ_names_to_string univs1  in
            let uu____56230 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____56228
              lid.FStar_Ident.str uu____56230
          else
            (let uu____56235 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____56235)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____56241 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____56243 =
            let uu____56245 = FStar_Options.print_universes ()  in
            if uu____56245
            then
              let uu____56249 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____56249
            else ""  in
          let uu____56255 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____56241
            lid.FStar_Ident.str uu____56243 uu____56255
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____56261 = FStar_Options.print_universes ()  in
          if uu____56261
          then
            let uu____56265 = univ_names_to_string us  in
            let uu____56267 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____56265 uu____56267
          else
            (let uu____56272 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____56272)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____56276) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____56282 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____56282
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____56286) ->
          let uu____56295 =
            let uu____56297 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____56297 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____56295
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____56342) -> lift_wp
            | (uu____56349,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____56357 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____56357 with
           | (us,t) ->
               let uu____56369 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____56371 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____56373 = univ_names_to_string us  in
               let uu____56375 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____56369
                 uu____56371 uu____56373 uu____56375)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____56387 = FStar_Options.print_universes ()  in
          if uu____56387
          then
            let uu____56391 =
              let uu____56396 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____56396  in
            (match uu____56391 with
             | (univs2,t) ->
                 let uu____56410 =
                   let uu____56415 =
                     let uu____56416 = FStar_Syntax_Subst.compress t  in
                     uu____56416.FStar_Syntax_Syntax.n  in
                   match uu____56415 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____56445 -> failwith "impossible"  in
                 (match uu____56410 with
                  | (tps1,c1) ->
                      let uu____56454 = sli l  in
                      let uu____56456 = univ_names_to_string univs2  in
                      let uu____56458 = binders_to_string " " tps1  in
                      let uu____56461 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____56454
                        uu____56456 uu____56458 uu____56461))
          else
            (let uu____56466 = sli l  in
             let uu____56468 = binders_to_string " " tps  in
             let uu____56471 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____56466 uu____56468
               uu____56471)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____56480 =
            let uu____56482 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____56482  in
          let uu____56492 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____56480 uu____56492
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____56496 ->
        let uu____56499 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____56499 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____56516 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____56516 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____56527,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____56529;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____56531;
                        FStar_Syntax_Syntax.lbdef = uu____56532;
                        FStar_Syntax_Syntax.lbattrs = uu____56533;
                        FStar_Syntax_Syntax.lbpos = uu____56534;_}::[]),uu____56535)
        ->
        let uu____56558 = lbname_to_string lb  in
        let uu____56560 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____56558 uu____56560
    | uu____56563 ->
        let uu____56564 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____56564 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____56588 = sli m.FStar_Syntax_Syntax.name  in
    let uu____56590 =
      let uu____56592 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____56592 (FStar_String.concat "\n")  in
    let uu____56602 =
      let uu____56604 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____56604 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____56588
      uu____56590 uu____56602
  
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
          (let uu____56648 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____56648))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____56657 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____56657)));
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
           (let uu____56698 = f x  in
            FStar_Util.string_builder_append strb uu____56698);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____56707 = f x1  in
                 FStar_Util.string_builder_append strb uu____56707)) xs;
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
           (let uu____56754 = f x  in
            FStar_Util.string_builder_append strb uu____56754);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____56763 = f x1  in
                 FStar_Util.string_builder_append strb uu____56763)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____56785 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____56785
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_56798  ->
    match uu___442_56798 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____56814 =
          let uu____56816 =
            let uu____56818 =
              let uu____56820 =
                let uu____56822 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____56822 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____56820 ")"  in
            Prims.op_Hat " " uu____56818  in
          Prims.op_Hat h uu____56816  in
        Prims.op_Hat "(" uu____56814
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____56837 =
          let uu____56839 = emb_typ_to_string a  in
          let uu____56841 =
            let uu____56843 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____56843  in
          Prims.op_Hat uu____56839 uu____56841  in
        Prims.op_Hat "(" uu____56837
  