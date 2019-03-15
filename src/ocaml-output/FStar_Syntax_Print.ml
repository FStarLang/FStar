open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_51517  ->
    match uu___429_51517 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____51521 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____51521
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____51526 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____51526
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____51530 =
          let uu____51532 = delta_depth_to_string d  in
          Prims.op_Hat uu____51532 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____51530
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____51544 = FStar_Options.print_real_names ()  in
    if uu____51544
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51571 =
      let uu____51573 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____51573  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51571
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51583 = FStar_Options.print_real_names ()  in
    if uu____51583
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51596 =
      let uu____51598 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____51598  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51596
  
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
      | uu____51820 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____51833 -> failwith "get_lid"
  
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
  'Auu____51936 'Auu____51937 .
    ('Auu____51936,'Auu____51937) FStar_Util.either -> Prims.bool
  =
  fun uu___430_51947  ->
    match uu___430_51947 with
    | FStar_Util.Inl uu____51952 -> false
    | FStar_Util.Inr uu____51954 -> true
  
let filter_imp :
  'Auu____51961 .
    ('Auu____51961 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51961 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_52016  ->
            match uu___431_52016 with
            | (uu____52024,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____52031,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____52032)) -> false
            | (uu____52037,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____52038)) -> false
            | uu____52044 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____52062 =
      let uu____52063 = FStar_Syntax_Subst.compress e  in
      uu____52063.FStar_Syntax_Syntax.n  in
    match uu____52062 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____52124 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____52124
        then
          let uu____52133 =
            let uu____52138 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____52138  in
          (match uu____52133 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____52149 =
                 let uu____52152 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____52152 :: xs  in
               FStar_Pervasives_Native.Some uu____52149
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____52164 ->
        let uu____52165 = is_lex_top e  in
        if uu____52165
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____52213 = f hd1  in if uu____52213 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____52245 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____52245
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52276 = get_lid e  in find_lid uu____52276 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52288 = get_lid e  in find_lid uu____52288 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____52300 = get_lid t  in find_lid uu____52300 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_52314  ->
    match uu___432_52314 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____52325 = FStar_Options.hide_uvar_nums ()  in
    if uu____52325
    then "?"
    else
      (let uu____52332 =
         let uu____52334 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____52334 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____52332)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____52346 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____52348 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____52346 uu____52348
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____52374 = FStar_Options.hide_uvar_nums ()  in
    if uu____52374
    then "?"
    else
      (let uu____52381 =
         let uu____52383 =
           let uu____52385 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____52385 FStar_Util.string_of_int  in
         let uu____52389 =
           let uu____52391 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____52391  in
         Prims.op_Hat uu____52383 uu____52389  in
       Prims.op_Hat "?" uu____52381)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____52419 = FStar_Syntax_Subst.compress_univ u  in
      match uu____52419 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____52432 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____52443 = FStar_Syntax_Subst.compress_univ u  in
    match uu____52443 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____52454 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____52454
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____52461 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____52461
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____52466 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____52466 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____52487 = univ_to_string u2  in
             let uu____52489 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____52487 uu____52489)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____52495 =
          let uu____52497 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____52497 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____52495
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____52516 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____52516 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____52533 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____52533 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_52551  ->
    match uu___433_52551 with
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
        let uu____52567 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____52567
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____52572 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____52572
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____52585 =
          let uu____52587 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52587  in
        let uu____52588 =
          let uu____52590 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52590 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____52585 uu____52588
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____52616 =
          let uu____52618 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52618  in
        let uu____52619 =
          let uu____52621 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52621 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____52616
          uu____52619
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____52638 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____52638
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
    | uu____52661 ->
        let uu____52664 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____52664 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____52692 ->
        let uu____52695 = quals_to_string quals  in
        Prims.op_Hat uu____52695 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____52891 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____52891
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____52895 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____52895
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____52899 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____52899
    | FStar_Syntax_Syntax.Tm_uinst uu____52902 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____52910 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____52912 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52914,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____52915;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52929,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____52930;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____52944 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____52964 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____52980 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____52988 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____53006 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____53030 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____53058 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____53073 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____53087,m) ->
        let uu____53125 = FStar_ST.op_Bang m  in
        (match uu____53125 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____53161 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____53167,m) ->
        let uu____53173 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____53173
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____53177 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____53180 =
      let uu____53182 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____53182  in
    if uu____53180
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____53196 = FStar_Options.print_implicits ()  in
         if uu____53196 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____53204 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____53229,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____53255,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____53257;
             FStar_Syntax_Syntax.rng = uu____53258;_}
           ->
           let uu____53269 =
             let uu____53271 =
               let uu____53273 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____53273  in
             Prims.op_Hat uu____53271 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____53269
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____53279 =
             let uu____53281 =
               let uu____53283 =
                 let uu____53284 =
                   let uu____53293 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____53293  in
                 uu____53284 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____53283  in
             Prims.op_Hat uu____53281 "]"  in
           Prims.op_Hat "[lazy:" uu____53279
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____53362 =
                  match uu____53362 with
                  | (bv,t) ->
                      let uu____53370 = bv_to_string bv  in
                      let uu____53372 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____53370 uu____53372
                   in
                let uu____53375 = term_to_string tm  in
                let uu____53377 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____53375 uu____53377
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____53386 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____53386)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____53409 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____53446 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____53471  ->
                                 match uu____53471 with
                                 | (t1,uu____53480) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____53446
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____53409 (FStar_String.concat "\\/")  in
           let uu____53495 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____53495
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____53509 = tag_of_term t  in
           let uu____53511 = sli m  in
           let uu____53513 = term_to_string t'  in
           let uu____53515 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____53509
             uu____53511 uu____53513 uu____53515
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____53530 = tag_of_term t  in
           let uu____53532 = term_to_string t'  in
           let uu____53534 = sli m0  in
           let uu____53536 = sli m1  in
           let uu____53538 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____53530 uu____53532 uu____53534 uu____53536 uu____53538
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____53553 = FStar_Range.string_of_range r  in
           let uu____53555 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____53553
             uu____53555
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____53564 = lid_to_string l  in
           let uu____53566 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____53568 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____53564
             uu____53566 uu____53568
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____53572) ->
           let uu____53577 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____53577
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____53581 = db_to_string x3  in
           let uu____53583 =
             let uu____53585 =
               let uu____53587 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____53587 ")"  in
             Prims.op_Hat ":(" uu____53585  in
           Prims.op_Hat uu____53581 uu____53583
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____53594)) ->
           let uu____53609 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53609
           then ctx_uvar_to_string u
           else
             (let uu____53615 =
                let uu____53617 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53617  in
              Prims.op_Hat "?" uu____53615)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____53640 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53640
           then
             let uu____53644 = ctx_uvar_to_string u  in
             let uu____53646 =
               let uu____53648 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____53648 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____53644 uu____53646
           else
             (let uu____53667 =
                let uu____53669 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53669  in
              Prims.op_Hat "?" uu____53667)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____53676 = FStar_Options.print_universes ()  in
           if uu____53676
           then
             let uu____53680 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____53680
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____53708 = binders_to_string " -> " bs  in
           let uu____53711 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____53708 uu____53711
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____53743 = binders_to_string " " bs  in
                let uu____53746 = term_to_string t2  in
                let uu____53748 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____53757 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____53757)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____53743 uu____53746
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____53748
            | uu____53761 ->
                let uu____53764 = binders_to_string " " bs  in
                let uu____53767 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____53764 uu____53767)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____53776 = bv_to_string xt  in
           let uu____53778 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____53781 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____53776 uu____53778
             uu____53781
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____53813 = term_to_string t  in
           let uu____53815 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____53813 uu____53815
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____53838 = lbs_to_string [] lbs  in
           let uu____53840 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____53838 uu____53840
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____53905 =
                   let uu____53907 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____53907
                     (FStar_Util.dflt "default")
                    in
                 let uu____53918 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____53905 uu____53918
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____53939 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____53939
              in
           let uu____53942 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____53942 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____53983 = term_to_string head1  in
           let uu____53985 =
             let uu____53987 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____54020  ->
                       match uu____54020 with
                       | (p,wopt,e) ->
                           let uu____54037 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____54040 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____54045 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____54045
                              in
                           let uu____54049 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____54037
                             uu____54040 uu____54049))
                in
             FStar_Util.concat_l "\n\t|" uu____53987  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____53983
             uu____53985
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____54061 = FStar_Options.print_universes ()  in
           if uu____54061
           then
             let uu____54065 = term_to_string t  in
             let uu____54067 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____54065 uu____54067
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____54074 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____54077 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____54079 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____54074 uu____54077
      uu____54079

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_54082  ->
    match uu___434_54082 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____54088 = FStar_Util.string_of_int i  in
        let uu____54090 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____54088 uu____54090
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____54097 = bv_to_string x  in
        let uu____54099 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____54097 uu____54099
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____54108 = bv_to_string x  in
        let uu____54110 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____54108 uu____54110
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____54117 = FStar_Util.string_of_int i  in
        let uu____54119 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____54117 uu____54119
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____54126 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____54126

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____54130 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____54130 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____54146 =
      let uu____54148 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54148  in
    if uu____54146
    then
      let e =
        let uu____54153 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____54153  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____54182 = fv_to_string l  in
           let uu____54184 =
             let uu____54186 =
               FStar_List.map
                 (fun uu____54200  ->
                    match uu____54200 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____54186 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____54182 uu____54184
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____54225) ->
           let uu____54230 = FStar_Options.print_bound_var_types ()  in
           if uu____54230
           then
             let uu____54234 = bv_to_string x1  in
             let uu____54236 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____54234 uu____54236
           else
             (let uu____54241 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____54241)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____54245 = FStar_Options.print_bound_var_types ()  in
           if uu____54245
           then
             let uu____54249 = bv_to_string x1  in
             let uu____54251 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____54249 uu____54251
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____54258 = FStar_Options.print_bound_var_types ()  in
           if uu____54258
           then
             let uu____54262 = bv_to_string x1  in
             let uu____54264 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____54262 uu____54264
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____54273 = quals_to_string' quals  in
      let uu____54275 =
        let uu____54277 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____54297 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____54299 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____54301 =
                    let uu____54303 = FStar_Options.print_universes ()  in
                    if uu____54303
                    then
                      let uu____54307 =
                        let uu____54309 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____54309 ">"  in
                      Prims.op_Hat "<" uu____54307
                    else ""  in
                  let uu____54316 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____54318 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____54297
                    uu____54299 uu____54301 uu____54316 uu____54318))
           in
        FStar_Util.concat_l "\n and " uu____54277  in
      FStar_Util.format3 "%slet %s %s" uu____54273
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____54275

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_54333  ->
    match uu___435_54333 with
    | [] -> ""
    | tms ->
        let uu____54341 =
          let uu____54343 =
            FStar_List.map
              (fun t  ->
                 let uu____54351 = term_to_string t  in paren uu____54351)
              tms
             in
          FStar_All.pipe_right uu____54343 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____54341

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____54360 = FStar_Options.print_effect_args ()  in
    if uu____54360
    then
      let uu____54364 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____54364
    else
      (let uu____54367 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____54369 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____54367 uu____54369)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_54373  ->
      match uu___436_54373 with
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
          let uu____54391 =
            let uu____54393 = term_to_string t  in
            Prims.op_Hat uu____54393 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____54391
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
      let uu____54413 =
        let uu____54415 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____54415  in
      if uu____54413
      then
        let uu____54419 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____54419 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____54430 = b  in
         match uu____54430 with
         | (a,imp) ->
             let uu____54444 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____54444
             then
               let uu____54448 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____54448
             else
               (let uu____54453 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____54456 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____54456)
                   in
                if uu____54453
                then
                  let uu____54460 = nm_to_string a  in
                  imp_to_string uu____54460 imp
                else
                  (let uu____54464 =
                     let uu____54466 = nm_to_string a  in
                     let uu____54468 =
                       let uu____54470 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____54470  in
                     Prims.op_Hat uu____54466 uu____54468  in
                   imp_to_string uu____54464 imp)))

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
        let uu____54489 = FStar_Options.print_implicits ()  in
        if uu____54489 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____54500 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____54500 (FStar_String.concat sep)
      else
        (let uu____54528 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____54528 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_54542  ->
    match uu___437_54542 with
    | (a,imp) ->
        let uu____54556 = term_to_string a  in imp_to_string uu____54556 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____54568 = FStar_Options.print_implicits ()  in
      if uu____54568 then args else filter_imp args  in
    let uu____54583 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____54583 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____54612 = FStar_Options.ugly ()  in
      if uu____54612
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____54623 =
      let uu____54625 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54625  in
    if uu____54623
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____54646 =
             let uu____54647 = FStar_Syntax_Subst.compress t  in
             uu____54647.FStar_Syntax_Syntax.n  in
           (match uu____54646 with
            | FStar_Syntax_Syntax.Tm_type uu____54651 when
                let uu____54652 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____54652 -> term_to_string t
            | uu____54654 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____54657 = univ_to_string u  in
                     let uu____54659 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____54657 uu____54659
                 | uu____54662 ->
                     let uu____54665 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____54665))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____54678 =
             let uu____54679 = FStar_Syntax_Subst.compress t  in
             uu____54679.FStar_Syntax_Syntax.n  in
           (match uu____54678 with
            | FStar_Syntax_Syntax.Tm_type uu____54683 when
                let uu____54684 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____54684 -> term_to_string t
            | uu____54686 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____54689 = univ_to_string u  in
                     let uu____54691 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____54689 uu____54691
                 | uu____54694 ->
                     let uu____54697 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____54697))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____54703 = FStar_Options.print_effect_args ()  in
             if uu____54703
             then
               let uu____54707 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____54709 =
                 let uu____54711 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____54711 (FStar_String.concat ", ")
                  in
               let uu____54726 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____54728 =
                 let uu____54730 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____54730 (FStar_String.concat ", ")
                  in
               let uu____54757 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____54707 uu____54709 uu____54726 uu____54728 uu____54757
             else
               (let uu____54762 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_54768  ->
                           match uu___438_54768 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____54771 -> false)))
                    &&
                    (let uu____54774 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____54774)
                   in
                if uu____54762
                then
                  let uu____54778 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____54778
                else
                  (let uu____54783 =
                     ((let uu____54787 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____54787) &&
                        (let uu____54790 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____54790))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____54783
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____54796 =
                        (let uu____54800 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____54800) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_54806  ->
                                   match uu___439_54806 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____54809 -> false)))
                         in
                      if uu____54796
                      then
                        let uu____54813 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____54813
                      else
                        (let uu____54818 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____54820 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____54818 uu____54820))))
              in
           let dec =
             let uu____54825 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_54838  ->
                       match uu___440_54838 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____54845 =
                             let uu____54847 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____54847
                              in
                           [uu____54845]
                       | uu____54852 -> []))
                in
             FStar_All.pipe_right uu____54825 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____54871 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_54881  ->
    match uu___441_54881 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____54898 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____54935 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____54960  ->
                              match uu____54960 with
                              | (t,uu____54969) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____54935
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____54898 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____54986 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____54986
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____54991) ->
        let uu____54996 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____54996
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____55007 = sli m  in
        let uu____55009 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____55007 uu____55009
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____55019 = sli m  in
        let uu____55021 = sli m'  in
        let uu____55023 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____55019
          uu____55021 uu____55023

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____55038 = FStar_Options.ugly ()  in
      if uu____55038
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
      let uu____55059 = b  in
      match uu____55059 with
      | (a,imp) ->
          let n1 =
            let uu____55067 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____55067
            then FStar_Util.JsonNull
            else
              (let uu____55072 =
                 let uu____55074 = nm_to_string a  in
                 imp_to_string uu____55074 imp  in
               FStar_Util.JsonStr uu____55072)
             in
          let t =
            let uu____55077 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____55077  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____55109 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____55109
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____55127 = FStar_Options.print_universes ()  in
    if uu____55127 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____55143 =
      let uu____55145 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____55145  in
    if uu____55143
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____55155 = s  in
       match uu____55155 with
       | (us,t) ->
           let uu____55167 =
             let uu____55169 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____55169  in
           let uu____55173 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____55167 uu____55173)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____55183 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____55185 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____55188 =
      let uu____55190 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____55190  in
    let uu____55194 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____55196 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____55183 uu____55185
      uu____55188 uu____55194 uu____55196
  
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
          let uu____55227 =
            let uu____55229 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____55229  in
          if uu____55227
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____55250 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____55250 (FStar_String.concat ",\n\t")
                in
             let uu____55265 =
               let uu____55269 =
                 let uu____55273 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____55275 =
                   let uu____55279 =
                     let uu____55281 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____55281  in
                   let uu____55285 =
                     let uu____55289 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____55292 =
                       let uu____55296 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____55298 =
                         let uu____55302 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____55304 =
                           let uu____55308 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____55310 =
                             let uu____55314 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____55316 =
                               let uu____55320 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____55322 =
                                 let uu____55326 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____55328 =
                                   let uu____55332 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____55334 =
                                     let uu____55338 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____55340 =
                                       let uu____55344 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____55346 =
                                         let uu____55350 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____55352 =
                                           let uu____55356 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____55358 =
                                             let uu____55362 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____55364 =
                                               let uu____55368 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____55370 =
                                                 let uu____55374 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____55376 =
                                                   let uu____55380 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____55380]  in
                                                 uu____55374 :: uu____55376
                                                  in
                                               uu____55368 :: uu____55370  in
                                             uu____55362 :: uu____55364  in
                                           uu____55356 :: uu____55358  in
                                         uu____55350 :: uu____55352  in
                                       uu____55344 :: uu____55346  in
                                     uu____55338 :: uu____55340  in
                                   uu____55332 :: uu____55334  in
                                 uu____55326 :: uu____55328  in
                               uu____55320 :: uu____55322  in
                             uu____55314 :: uu____55316  in
                           uu____55308 :: uu____55310  in
                         uu____55302 :: uu____55304  in
                       uu____55296 :: uu____55298  in
                     uu____55289 :: uu____55292  in
                   uu____55279 :: uu____55285  in
                 uu____55273 :: uu____55275  in
               (if for_free then "_for_free " else "") :: uu____55269  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____55265)
  
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
          (lid,univs1,tps,k,uu____55454,uu____55455) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____55471 = FStar_Options.print_universes ()  in
          if uu____55471
          then
            let uu____55475 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____55475 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____55484,uu____55485,uu____55486) ->
          let uu____55493 = FStar_Options.print_universes ()  in
          if uu____55493
          then
            let uu____55497 = univ_names_to_string univs1  in
            let uu____55499 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____55497
              lid.FStar_Ident.str uu____55499
          else
            (let uu____55504 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____55504)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____55510 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____55512 =
            let uu____55514 = FStar_Options.print_universes ()  in
            if uu____55514
            then
              let uu____55518 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____55518
            else ""  in
          let uu____55524 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____55510
            lid.FStar_Ident.str uu____55512 uu____55524
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____55530 = FStar_Options.print_universes ()  in
          if uu____55530
          then
            let uu____55534 = univ_names_to_string us  in
            let uu____55536 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____55534 uu____55536
          else
            (let uu____55541 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____55541)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____55545) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____55551 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____55551
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____55555) ->
          let uu____55564 =
            let uu____55566 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____55566 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____55564
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____55611) -> lift_wp
            | (uu____55618,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____55626 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____55626 with
           | (us,t) ->
               let uu____55638 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____55640 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____55642 = univ_names_to_string us  in
               let uu____55644 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____55638
                 uu____55640 uu____55642 uu____55644)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____55656 = FStar_Options.print_universes ()  in
          if uu____55656
          then
            let uu____55660 =
              let uu____55665 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____55665  in
            (match uu____55660 with
             | (univs2,t) ->
                 let uu____55679 =
                   let uu____55684 =
                     let uu____55685 = FStar_Syntax_Subst.compress t  in
                     uu____55685.FStar_Syntax_Syntax.n  in
                   match uu____55684 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____55714 -> failwith "impossible"  in
                 (match uu____55679 with
                  | (tps1,c1) ->
                      let uu____55723 = sli l  in
                      let uu____55725 = univ_names_to_string univs2  in
                      let uu____55727 = binders_to_string " " tps1  in
                      let uu____55730 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____55723
                        uu____55725 uu____55727 uu____55730))
          else
            (let uu____55735 = sli l  in
             let uu____55737 = binders_to_string " " tps  in
             let uu____55740 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____55735 uu____55737
               uu____55740)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____55749 =
            let uu____55751 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____55751  in
          let uu____55761 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____55749 uu____55761
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____55765 ->
        let uu____55768 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____55768 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____55785 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____55785 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____55796,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____55798;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____55800;
                        FStar_Syntax_Syntax.lbdef = uu____55801;
                        FStar_Syntax_Syntax.lbattrs = uu____55802;
                        FStar_Syntax_Syntax.lbpos = uu____55803;_}::[]),uu____55804)
        ->
        let uu____55827 = lbname_to_string lb  in
        let uu____55829 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____55827 uu____55829
    | uu____55832 ->
        let uu____55833 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____55833 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____55857 = sli m.FStar_Syntax_Syntax.name  in
    let uu____55859 =
      let uu____55861 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____55861 (FStar_String.concat "\n")  in
    let uu____55871 =
      let uu____55873 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____55873 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____55857
      uu____55859 uu____55871
  
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
          (let uu____55917 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____55917))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____55926 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____55926)));
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
           (let uu____55967 = f x  in
            FStar_Util.string_builder_append strb uu____55967);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____55976 = f x1  in
                 FStar_Util.string_builder_append strb uu____55976)) xs;
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
           (let uu____56023 = f x  in
            FStar_Util.string_builder_append strb uu____56023);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____56032 = f x1  in
                 FStar_Util.string_builder_append strb uu____56032)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____56054 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____56054
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_56067  ->
    match uu___442_56067 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____56083 =
          let uu____56085 =
            let uu____56087 =
              let uu____56089 =
                let uu____56091 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____56091 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____56089 ")"  in
            Prims.op_Hat " " uu____56087  in
          Prims.op_Hat h uu____56085  in
        Prims.op_Hat "(" uu____56083
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____56106 =
          let uu____56108 = emb_typ_to_string a  in
          let uu____56110 =
            let uu____56112 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____56112  in
          Prims.op_Hat uu____56108 uu____56110  in
        Prims.op_Hat "(" uu____56106
  