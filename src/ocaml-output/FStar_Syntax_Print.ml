open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_51530  ->
    match uu___429_51530 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____51534 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____51534
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____51539 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____51539
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____51543 =
          let uu____51545 = delta_depth_to_string d  in
          Prims.op_Hat uu____51545 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____51543
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____51557 = FStar_Options.print_real_names ()  in
    if uu____51557
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51584 =
      let uu____51586 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____51586  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51584
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51596 = FStar_Options.print_real_names ()  in
    if uu____51596
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51609 =
      let uu____51611 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____51611  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51609
  
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
      | uu____51833 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____51846 -> failwith "get_lid"
  
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
  'Auu____51949 'Auu____51950 .
    ('Auu____51949,'Auu____51950) FStar_Util.either -> Prims.bool
  =
  fun uu___430_51960  ->
    match uu___430_51960 with
    | FStar_Util.Inl uu____51965 -> false
    | FStar_Util.Inr uu____51967 -> true
  
let filter_imp :
  'Auu____51974 .
    ('Auu____51974 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51974 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_52029  ->
            match uu___431_52029 with
            | (uu____52037,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____52044,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____52045)) -> false
            | (uu____52050,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____52051)) -> false
            | uu____52057 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____52075 =
      let uu____52076 = FStar_Syntax_Subst.compress e  in
      uu____52076.FStar_Syntax_Syntax.n  in
    match uu____52075 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____52137 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____52137
        then
          let uu____52146 =
            let uu____52151 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____52151  in
          (match uu____52146 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____52162 =
                 let uu____52165 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____52165 :: xs  in
               FStar_Pervasives_Native.Some uu____52162
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____52177 ->
        let uu____52178 = is_lex_top e  in
        if uu____52178
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____52226 = f hd1  in if uu____52226 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____52258 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____52258
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52289 = get_lid e  in find_lid uu____52289 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52301 = get_lid e  in find_lid uu____52301 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____52313 = get_lid t  in find_lid uu____52313 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_52327  ->
    match uu___432_52327 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____52338 = FStar_Options.hide_uvar_nums ()  in
    if uu____52338
    then "?"
    else
      (let uu____52345 =
         let uu____52347 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____52347 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____52345)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____52359 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____52361 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____52359 uu____52361
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____52387 = FStar_Options.hide_uvar_nums ()  in
    if uu____52387
    then "?"
    else
      (let uu____52394 =
         let uu____52396 =
           let uu____52398 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____52398 FStar_Util.string_of_int  in
         let uu____52402 =
           let uu____52404 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____52404  in
         Prims.op_Hat uu____52396 uu____52402  in
       Prims.op_Hat "?" uu____52394)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____52432 = FStar_Syntax_Subst.compress_univ u  in
      match uu____52432 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____52445 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____52456 = FStar_Syntax_Subst.compress_univ u  in
    match uu____52456 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____52467 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____52467
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____52474 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____52474
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____52479 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____52479 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____52500 = univ_to_string u2  in
             let uu____52502 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____52500 uu____52502)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____52508 =
          let uu____52510 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____52510 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____52508
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____52529 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____52529 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____52546 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____52546 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_52564  ->
    match uu___433_52564 with
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
        let uu____52580 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____52580
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____52585 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____52585
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____52598 =
          let uu____52600 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52600  in
        let uu____52601 =
          let uu____52603 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52603 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____52598 uu____52601
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____52629 =
          let uu____52631 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52631  in
        let uu____52632 =
          let uu____52634 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52634 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____52629
          uu____52632
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____52651 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____52651
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
    | uu____52674 ->
        let uu____52677 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____52677 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____52705 ->
        let uu____52708 = quals_to_string quals  in
        Prims.op_Hat uu____52708 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____52904 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____52904
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____52908 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____52908
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____52912 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____52912
    | FStar_Syntax_Syntax.Tm_uinst uu____52915 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____52923 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____52925 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52927,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____52928;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52942,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____52943;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____52957 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____52977 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____52993 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____53001 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____53019 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____53043 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____53071 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____53086 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____53100,m) ->
        let uu____53138 = FStar_ST.op_Bang m  in
        (match uu____53138 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____53174 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____53180,m) ->
        let uu____53186 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____53186
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____53190 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____53193 =
      let uu____53195 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____53195  in
    if uu____53193
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____53209 = FStar_Options.print_implicits ()  in
         if uu____53209 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____53217 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____53242,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____53268,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____53270;
             FStar_Syntax_Syntax.rng = uu____53271;_}
           ->
           let uu____53282 =
             let uu____53284 =
               let uu____53286 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____53286  in
             Prims.op_Hat uu____53284 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____53282
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____53292 =
             let uu____53294 =
               let uu____53296 =
                 let uu____53297 =
                   let uu____53306 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____53306  in
                 uu____53297 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____53296  in
             Prims.op_Hat uu____53294 "]"  in
           Prims.op_Hat "[lazy:" uu____53292
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____53375 =
                  match uu____53375 with
                  | (bv,t) ->
                      let uu____53383 = bv_to_string bv  in
                      let uu____53385 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____53383 uu____53385
                   in
                let uu____53388 = term_to_string tm  in
                let uu____53390 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____53388 uu____53390
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____53399 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____53399)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____53422 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____53459 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____53484  ->
                                 match uu____53484 with
                                 | (t1,uu____53493) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____53459
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____53422 (FStar_String.concat "\\/")  in
           let uu____53508 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____53508
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____53522 = tag_of_term t  in
           let uu____53524 = sli m  in
           let uu____53526 = term_to_string t'  in
           let uu____53528 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____53522
             uu____53524 uu____53526 uu____53528
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____53543 = tag_of_term t  in
           let uu____53545 = term_to_string t'  in
           let uu____53547 = sli m0  in
           let uu____53549 = sli m1  in
           let uu____53551 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____53543 uu____53545 uu____53547 uu____53549 uu____53551
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____53566 = FStar_Range.string_of_range r  in
           let uu____53568 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____53566
             uu____53568
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____53577 = lid_to_string l  in
           let uu____53579 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____53581 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____53577
             uu____53579 uu____53581
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____53585) ->
           let uu____53590 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____53590
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____53594 = db_to_string x3  in
           let uu____53596 =
             let uu____53598 =
               let uu____53600 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____53600 ")"  in
             Prims.op_Hat ":(" uu____53598  in
           Prims.op_Hat uu____53594 uu____53596
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____53607)) ->
           let uu____53622 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53622
           then ctx_uvar_to_string u
           else
             (let uu____53628 =
                let uu____53630 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53630  in
              Prims.op_Hat "?" uu____53628)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____53653 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53653
           then
             let uu____53657 = ctx_uvar_to_string u  in
             let uu____53659 =
               let uu____53661 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____53661 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____53657 uu____53659
           else
             (let uu____53680 =
                let uu____53682 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53682  in
              Prims.op_Hat "?" uu____53680)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____53689 = FStar_Options.print_universes ()  in
           if uu____53689
           then
             let uu____53693 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____53693
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____53721 = binders_to_string " -> " bs  in
           let uu____53724 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____53721 uu____53724
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____53756 = binders_to_string " " bs  in
                let uu____53759 = term_to_string t2  in
                let uu____53761 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____53770 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____53770)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____53756 uu____53759
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____53761
            | uu____53774 ->
                let uu____53777 = binders_to_string " " bs  in
                let uu____53780 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____53777 uu____53780)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____53789 = bv_to_string xt  in
           let uu____53791 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____53794 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____53789 uu____53791
             uu____53794
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____53826 = term_to_string t  in
           let uu____53828 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____53826 uu____53828
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____53851 = lbs_to_string [] lbs  in
           let uu____53853 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____53851 uu____53853
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____53918 =
                   let uu____53920 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____53920
                     (FStar_Util.dflt "default")
                    in
                 let uu____53931 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____53918 uu____53931
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____53952 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____53952
              in
           let uu____53955 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____53955 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____53996 = term_to_string head1  in
           let uu____53998 =
             let uu____54000 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____54033  ->
                       match uu____54033 with
                       | (p,wopt,e) ->
                           let uu____54050 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____54053 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____54058 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____54058
                              in
                           let uu____54062 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____54050
                             uu____54053 uu____54062))
                in
             FStar_Util.concat_l "\n\t|" uu____54000  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____53996
             uu____53998
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____54074 = FStar_Options.print_universes ()  in
           if uu____54074
           then
             let uu____54078 = term_to_string t  in
             let uu____54080 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____54078 uu____54080
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____54087 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____54090 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____54092 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____54087 uu____54090
      uu____54092

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_54095  ->
    match uu___434_54095 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____54101 = FStar_Util.string_of_int i  in
        let uu____54103 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____54101 uu____54103
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____54110 = bv_to_string x  in
        let uu____54112 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____54110 uu____54112
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____54121 = bv_to_string x  in
        let uu____54123 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____54121 uu____54123
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____54130 = FStar_Util.string_of_int i  in
        let uu____54132 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____54130 uu____54132
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____54139 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____54139

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____54143 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____54143 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____54159 =
      let uu____54161 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54161  in
    if uu____54159
    then
      let e =
        let uu____54166 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____54166  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____54195 = fv_to_string l  in
           let uu____54197 =
             let uu____54199 =
               FStar_List.map
                 (fun uu____54213  ->
                    match uu____54213 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____54199 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____54195 uu____54197
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____54238) ->
           let uu____54243 = FStar_Options.print_bound_var_types ()  in
           if uu____54243
           then
             let uu____54247 = bv_to_string x1  in
             let uu____54249 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____54247 uu____54249
           else
             (let uu____54254 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____54254)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____54258 = FStar_Options.print_bound_var_types ()  in
           if uu____54258
           then
             let uu____54262 = bv_to_string x1  in
             let uu____54264 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____54262 uu____54264
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____54271 = FStar_Options.print_bound_var_types ()  in
           if uu____54271
           then
             let uu____54275 = bv_to_string x1  in
             let uu____54277 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____54275 uu____54277
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____54286 = quals_to_string' quals  in
      let uu____54288 =
        let uu____54290 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____54310 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____54312 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____54314 =
                    let uu____54316 = FStar_Options.print_universes ()  in
                    if uu____54316
                    then
                      let uu____54320 =
                        let uu____54322 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____54322 ">"  in
                      Prims.op_Hat "<" uu____54320
                    else ""  in
                  let uu____54329 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____54331 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____54310
                    uu____54312 uu____54314 uu____54329 uu____54331))
           in
        FStar_Util.concat_l "\n and " uu____54290  in
      FStar_Util.format3 "%slet %s %s" uu____54286
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____54288

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_54346  ->
    match uu___435_54346 with
    | [] -> ""
    | tms ->
        let uu____54354 =
          let uu____54356 =
            FStar_List.map
              (fun t  ->
                 let uu____54364 = term_to_string t  in paren uu____54364)
              tms
             in
          FStar_All.pipe_right uu____54356 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____54354

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____54373 = FStar_Options.print_effect_args ()  in
    if uu____54373
    then
      let uu____54377 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____54377
    else
      (let uu____54380 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____54382 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____54380 uu____54382)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_54386  ->
      match uu___436_54386 with
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
          let uu____54404 =
            let uu____54406 = term_to_string t  in
            Prims.op_Hat uu____54406 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____54404
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
      let uu____54426 =
        let uu____54428 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____54428  in
      if uu____54426
      then
        let uu____54432 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____54432 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____54443 = b  in
         match uu____54443 with
         | (a,imp) ->
             let uu____54457 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____54457
             then
               let uu____54461 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____54461
             else
               (let uu____54466 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____54469 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____54469)
                   in
                if uu____54466
                then
                  let uu____54473 = nm_to_string a  in
                  imp_to_string uu____54473 imp
                else
                  (let uu____54477 =
                     let uu____54479 = nm_to_string a  in
                     let uu____54481 =
                       let uu____54483 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____54483  in
                     Prims.op_Hat uu____54479 uu____54481  in
                   imp_to_string uu____54477 imp)))

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
        let uu____54502 = FStar_Options.print_implicits ()  in
        if uu____54502 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____54513 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____54513 (FStar_String.concat sep)
      else
        (let uu____54541 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____54541 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_54555  ->
    match uu___437_54555 with
    | (a,imp) ->
        let uu____54569 = term_to_string a  in imp_to_string uu____54569 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____54581 = FStar_Options.print_implicits ()  in
      if uu____54581 then args else filter_imp args  in
    let uu____54596 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____54596 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____54625 = FStar_Options.ugly ()  in
      if uu____54625
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____54636 =
      let uu____54638 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54638  in
    if uu____54636
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____54659 =
             let uu____54660 = FStar_Syntax_Subst.compress t  in
             uu____54660.FStar_Syntax_Syntax.n  in
           (match uu____54659 with
            | FStar_Syntax_Syntax.Tm_type uu____54664 when
                let uu____54665 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____54665 -> term_to_string t
            | uu____54667 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____54670 = univ_to_string u  in
                     let uu____54672 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____54670 uu____54672
                 | uu____54675 ->
                     let uu____54678 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____54678))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____54691 =
             let uu____54692 = FStar_Syntax_Subst.compress t  in
             uu____54692.FStar_Syntax_Syntax.n  in
           (match uu____54691 with
            | FStar_Syntax_Syntax.Tm_type uu____54696 when
                let uu____54697 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____54697 -> term_to_string t
            | uu____54699 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____54702 = univ_to_string u  in
                     let uu____54704 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____54702 uu____54704
                 | uu____54707 ->
                     let uu____54710 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____54710))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____54716 = FStar_Options.print_effect_args ()  in
             if uu____54716
             then
               let uu____54720 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____54722 =
                 let uu____54724 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____54724 (FStar_String.concat ", ")
                  in
               let uu____54739 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____54741 =
                 let uu____54743 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____54743 (FStar_String.concat ", ")
                  in
               let uu____54770 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____54720 uu____54722 uu____54739 uu____54741 uu____54770
             else
               (let uu____54775 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_54781  ->
                           match uu___438_54781 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____54784 -> false)))
                    &&
                    (let uu____54787 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____54787)
                   in
                if uu____54775
                then
                  let uu____54791 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____54791
                else
                  (let uu____54796 =
                     ((let uu____54800 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____54800) &&
                        (let uu____54803 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____54803))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____54796
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____54809 =
                        (let uu____54813 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____54813) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_54819  ->
                                   match uu___439_54819 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____54822 -> false)))
                         in
                      if uu____54809
                      then
                        let uu____54826 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____54826
                      else
                        (let uu____54831 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____54833 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____54831 uu____54833))))
              in
           let dec =
             let uu____54838 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_54851  ->
                       match uu___440_54851 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____54858 =
                             let uu____54860 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____54860
                              in
                           [uu____54858]
                       | uu____54865 -> []))
                in
             FStar_All.pipe_right uu____54838 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____54884 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_54894  ->
    match uu___441_54894 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____54911 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____54948 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____54973  ->
                              match uu____54973 with
                              | (t,uu____54982) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____54948
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____54911 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____54999 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____54999
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____55004) ->
        let uu____55009 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____55009
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____55020 = sli m  in
        let uu____55022 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____55020 uu____55022
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____55032 = sli m  in
        let uu____55034 = sli m'  in
        let uu____55036 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____55032
          uu____55034 uu____55036

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____55051 = FStar_Options.ugly ()  in
      if uu____55051
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
      let uu____55072 = b  in
      match uu____55072 with
      | (a,imp) ->
          let n1 =
            let uu____55080 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____55080
            then FStar_Util.JsonNull
            else
              (let uu____55085 =
                 let uu____55087 = nm_to_string a  in
                 imp_to_string uu____55087 imp  in
               FStar_Util.JsonStr uu____55085)
             in
          let t =
            let uu____55090 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____55090  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____55122 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____55122
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____55140 = FStar_Options.print_universes ()  in
    if uu____55140 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____55156 =
      let uu____55158 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____55158  in
    if uu____55156
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____55168 = s  in
       match uu____55168 with
       | (us,t) ->
           let uu____55180 =
             let uu____55182 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____55182  in
           let uu____55186 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____55180 uu____55186)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____55196 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____55198 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____55201 =
      let uu____55203 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____55203  in
    let uu____55207 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____55209 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____55196 uu____55198
      uu____55201 uu____55207 uu____55209
  
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
          let uu____55240 =
            let uu____55242 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____55242  in
          if uu____55240
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____55263 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____55263 (FStar_String.concat ",\n\t")
                in
             let uu____55278 =
               let uu____55282 =
                 let uu____55286 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____55288 =
                   let uu____55292 =
                     let uu____55294 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____55294  in
                   let uu____55298 =
                     let uu____55302 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____55305 =
                       let uu____55309 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____55311 =
                         let uu____55315 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____55317 =
                           let uu____55321 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____55323 =
                             let uu____55327 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____55329 =
                               let uu____55333 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____55335 =
                                 let uu____55339 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____55341 =
                                   let uu____55345 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____55347 =
                                     let uu____55351 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____55353 =
                                       let uu____55357 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____55359 =
                                         let uu____55363 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____55365 =
                                           let uu____55369 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____55371 =
                                             let uu____55375 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____55377 =
                                               let uu____55381 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____55383 =
                                                 let uu____55387 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____55389 =
                                                   let uu____55393 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____55393]  in
                                                 uu____55387 :: uu____55389
                                                  in
                                               uu____55381 :: uu____55383  in
                                             uu____55375 :: uu____55377  in
                                           uu____55369 :: uu____55371  in
                                         uu____55363 :: uu____55365  in
                                       uu____55357 :: uu____55359  in
                                     uu____55351 :: uu____55353  in
                                   uu____55345 :: uu____55347  in
                                 uu____55339 :: uu____55341  in
                               uu____55333 :: uu____55335  in
                             uu____55327 :: uu____55329  in
                           uu____55321 :: uu____55323  in
                         uu____55315 :: uu____55317  in
                       uu____55309 :: uu____55311  in
                     uu____55302 :: uu____55305  in
                   uu____55292 :: uu____55298  in
                 uu____55286 :: uu____55288  in
               (if for_free then "_for_free " else "") :: uu____55282  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____55278)
  
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
          (lid,univs1,tps,k,uu____55467,uu____55468) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____55484 = FStar_Options.print_universes ()  in
          if uu____55484
          then
            let uu____55488 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____55488 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____55497,uu____55498,uu____55499) ->
          let uu____55506 = FStar_Options.print_universes ()  in
          if uu____55506
          then
            let uu____55510 = univ_names_to_string univs1  in
            let uu____55512 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____55510
              lid.FStar_Ident.str uu____55512
          else
            (let uu____55517 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____55517)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____55523 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____55525 =
            let uu____55527 = FStar_Options.print_universes ()  in
            if uu____55527
            then
              let uu____55531 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____55531
            else ""  in
          let uu____55537 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____55523
            lid.FStar_Ident.str uu____55525 uu____55537
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____55543 = FStar_Options.print_universes ()  in
          if uu____55543
          then
            let uu____55547 = univ_names_to_string us  in
            let uu____55549 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____55547 uu____55549
          else
            (let uu____55554 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____55554)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____55558) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____55564 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____55564
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____55568) ->
          let uu____55577 =
            let uu____55579 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____55579 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____55577
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____55624) -> lift_wp
            | (uu____55631,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____55639 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____55639 with
           | (us,t) ->
               let uu____55651 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____55653 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____55655 = univ_names_to_string us  in
               let uu____55657 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____55651
                 uu____55653 uu____55655 uu____55657)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____55669 = FStar_Options.print_universes ()  in
          if uu____55669
          then
            let uu____55673 =
              let uu____55678 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____55678  in
            (match uu____55673 with
             | (univs2,t) ->
                 let uu____55692 =
                   let uu____55697 =
                     let uu____55698 = FStar_Syntax_Subst.compress t  in
                     uu____55698.FStar_Syntax_Syntax.n  in
                   match uu____55697 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____55727 -> failwith "impossible"  in
                 (match uu____55692 with
                  | (tps1,c1) ->
                      let uu____55736 = sli l  in
                      let uu____55738 = univ_names_to_string univs2  in
                      let uu____55740 = binders_to_string " " tps1  in
                      let uu____55743 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____55736
                        uu____55738 uu____55740 uu____55743))
          else
            (let uu____55748 = sli l  in
             let uu____55750 = binders_to_string " " tps  in
             let uu____55753 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____55748 uu____55750
               uu____55753)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____55762 =
            let uu____55764 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____55764  in
          let uu____55774 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____55762 uu____55774
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____55778 ->
        let uu____55781 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____55781 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____55798 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____55798 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____55809,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____55811;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____55813;
                        FStar_Syntax_Syntax.lbdef = uu____55814;
                        FStar_Syntax_Syntax.lbattrs = uu____55815;
                        FStar_Syntax_Syntax.lbpos = uu____55816;_}::[]),uu____55817)
        ->
        let uu____55840 = lbname_to_string lb  in
        let uu____55842 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____55840 uu____55842
    | uu____55845 ->
        let uu____55846 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____55846 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____55870 = sli m.FStar_Syntax_Syntax.name  in
    let uu____55872 =
      let uu____55874 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____55874 (FStar_String.concat "\n")  in
    let uu____55884 =
      let uu____55886 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____55886 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____55870
      uu____55872 uu____55884
  
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
          (let uu____55930 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____55930))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____55939 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____55939)));
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
           (let uu____55980 = f x  in
            FStar_Util.string_builder_append strb uu____55980);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____55989 = f x1  in
                 FStar_Util.string_builder_append strb uu____55989)) xs;
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
           (let uu____56036 = f x  in
            FStar_Util.string_builder_append strb uu____56036);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____56045 = f x1  in
                 FStar_Util.string_builder_append strb uu____56045)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____56067 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____56067
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_56080  ->
    match uu___442_56080 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____56096 =
          let uu____56098 =
            let uu____56100 =
              let uu____56102 =
                let uu____56104 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____56104 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____56102 ")"  in
            Prims.op_Hat " " uu____56100  in
          Prims.op_Hat h uu____56098  in
        Prims.op_Hat "(" uu____56096
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____56119 =
          let uu____56121 = emb_typ_to_string a  in
          let uu____56123 =
            let uu____56125 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____56125  in
          Prims.op_Hat uu____56121 uu____56123  in
        Prims.op_Hat "(" uu____56119
  