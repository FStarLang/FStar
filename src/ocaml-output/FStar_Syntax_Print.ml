open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_51549  ->
    match uu___429_51549 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____51553 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____51553
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____51558 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____51558
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____51562 =
          let uu____51564 = delta_depth_to_string d  in
          Prims.op_Hat uu____51564 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____51562
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____51576 = FStar_Options.print_real_names ()  in
    if uu____51576
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51603 =
      let uu____51605 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____51605  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51603
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51615 = FStar_Options.print_real_names ()  in
    if uu____51615
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51628 =
      let uu____51630 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____51630  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51628
  
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
      | uu____51852 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____51865 -> failwith "get_lid"
  
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
  'Auu____51968 'Auu____51969 .
    ('Auu____51968,'Auu____51969) FStar_Util.either -> Prims.bool
  =
  fun uu___430_51979  ->
    match uu___430_51979 with
    | FStar_Util.Inl uu____51984 -> false
    | FStar_Util.Inr uu____51986 -> true
  
let filter_imp :
  'Auu____51993 .
    ('Auu____51993 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51993 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_52048  ->
            match uu___431_52048 with
            | (uu____52056,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____52063,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____52064)) -> false
            | (uu____52069,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____52070)) -> false
            | uu____52076 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____52094 =
      let uu____52095 = FStar_Syntax_Subst.compress e  in
      uu____52095.FStar_Syntax_Syntax.n  in
    match uu____52094 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____52156 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____52156
        then
          let uu____52165 =
            let uu____52170 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____52170  in
          (match uu____52165 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____52181 =
                 let uu____52184 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____52184 :: xs  in
               FStar_Pervasives_Native.Some uu____52181
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____52196 ->
        let uu____52197 = is_lex_top e  in
        if uu____52197
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____52245 = f hd1  in if uu____52245 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____52277 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____52277
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52308 = get_lid e  in find_lid uu____52308 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52320 = get_lid e  in find_lid uu____52320 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____52332 = get_lid t  in find_lid uu____52332 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_52346  ->
    match uu___432_52346 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____52357 = FStar_Options.hide_uvar_nums ()  in
    if uu____52357
    then "?"
    else
      (let uu____52364 =
         let uu____52366 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____52366 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____52364)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____52378 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____52380 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____52378 uu____52380
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____52406 = FStar_Options.hide_uvar_nums ()  in
    if uu____52406
    then "?"
    else
      (let uu____52413 =
         let uu____52415 =
           let uu____52417 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____52417 FStar_Util.string_of_int  in
         let uu____52421 =
           let uu____52423 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____52423  in
         Prims.op_Hat uu____52415 uu____52421  in
       Prims.op_Hat "?" uu____52413)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____52451 = FStar_Syntax_Subst.compress_univ u  in
      match uu____52451 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____52464 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____52475 = FStar_Syntax_Subst.compress_univ u  in
    match uu____52475 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____52486 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____52486
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____52493 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____52493
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____52498 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____52498 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____52519 = univ_to_string u2  in
             let uu____52521 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____52519 uu____52521)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____52527 =
          let uu____52529 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____52529 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____52527
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____52548 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____52548 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____52565 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____52565 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_52583  ->
    match uu___433_52583 with
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
        let uu____52599 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____52599
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____52604 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____52604
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____52617 =
          let uu____52619 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52619  in
        let uu____52620 =
          let uu____52622 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52622 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____52617 uu____52620
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____52648 =
          let uu____52650 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52650  in
        let uu____52651 =
          let uu____52653 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52653 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____52648
          uu____52651
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____52670 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____52670
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
    | uu____52693 ->
        let uu____52696 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____52696 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____52724 ->
        let uu____52727 = quals_to_string quals  in
        Prims.op_Hat uu____52727 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____52923 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____52923
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____52927 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____52927
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____52931 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____52931
    | FStar_Syntax_Syntax.Tm_uinst uu____52934 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____52942 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____52944 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52946,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____52947;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52961,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____52962;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____52976 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____52996 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____53012 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____53020 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____53038 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____53062 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____53090 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____53105 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____53119,m) ->
        let uu____53157 = FStar_ST.op_Bang m  in
        (match uu____53157 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____53193 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____53199,m) ->
        let uu____53205 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____53205
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____53209 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____53212 =
      let uu____53214 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____53214  in
    if uu____53212
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____53228 = FStar_Options.print_implicits ()  in
         if uu____53228 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____53236 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____53261,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____53287,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____53289;
             FStar_Syntax_Syntax.rng = uu____53290;_}
           ->
           let uu____53301 =
             let uu____53303 =
               let uu____53305 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____53305  in
             Prims.op_Hat uu____53303 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____53301
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____53311 =
             let uu____53313 =
               let uu____53315 =
                 let uu____53316 =
                   let uu____53325 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____53325  in
                 uu____53316 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____53315  in
             Prims.op_Hat uu____53313 "]"  in
           Prims.op_Hat "[lazy:" uu____53311
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____53394 =
                  match uu____53394 with
                  | (bv,t) ->
                      let uu____53402 = bv_to_string bv  in
                      let uu____53404 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____53402 uu____53404
                   in
                let uu____53407 = term_to_string tm  in
                let uu____53409 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____53407 uu____53409
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____53418 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____53418)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____53441 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____53478 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____53503  ->
                                 match uu____53503 with
                                 | (t1,uu____53512) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____53478
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____53441 (FStar_String.concat "\\/")  in
           let uu____53527 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____53527
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____53541 = tag_of_term t  in
           let uu____53543 = sli m  in
           let uu____53545 = term_to_string t'  in
           let uu____53547 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____53541
             uu____53543 uu____53545 uu____53547
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____53562 = tag_of_term t  in
           let uu____53564 = term_to_string t'  in
           let uu____53566 = sli m0  in
           let uu____53568 = sli m1  in
           let uu____53570 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____53562 uu____53564 uu____53566 uu____53568 uu____53570
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____53585 = FStar_Range.string_of_range r  in
           let uu____53587 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____53585
             uu____53587
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____53596 = lid_to_string l  in
           let uu____53598 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____53600 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____53596
             uu____53598 uu____53600
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____53604) ->
           let uu____53609 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____53609
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____53613 = db_to_string x3  in
           let uu____53615 =
             let uu____53617 =
               let uu____53619 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____53619 ")"  in
             Prims.op_Hat ":(" uu____53617  in
           Prims.op_Hat uu____53613 uu____53615
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____53626)) ->
           let uu____53641 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53641
           then ctx_uvar_to_string u
           else
             (let uu____53647 =
                let uu____53649 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53649  in
              Prims.op_Hat "?" uu____53647)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____53672 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53672
           then
             let uu____53676 = ctx_uvar_to_string u  in
             let uu____53678 =
               let uu____53680 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____53680 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____53676 uu____53678
           else
             (let uu____53699 =
                let uu____53701 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53701  in
              Prims.op_Hat "?" uu____53699)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____53708 = FStar_Options.print_universes ()  in
           if uu____53708
           then
             let uu____53712 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____53712
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____53740 = binders_to_string " -> " bs  in
           let uu____53743 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____53740 uu____53743
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____53775 = binders_to_string " " bs  in
                let uu____53778 = term_to_string t2  in
                let uu____53780 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____53789 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____53789)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____53775 uu____53778
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____53780
            | uu____53793 ->
                let uu____53796 = binders_to_string " " bs  in
                let uu____53799 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____53796 uu____53799)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____53808 = bv_to_string xt  in
           let uu____53810 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____53813 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____53808 uu____53810
             uu____53813
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____53845 = term_to_string t  in
           let uu____53847 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____53845 uu____53847
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____53870 = lbs_to_string [] lbs  in
           let uu____53872 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____53870 uu____53872
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____53937 =
                   let uu____53939 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____53939
                     (FStar_Util.dflt "default")
                    in
                 let uu____53950 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____53937 uu____53950
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____53971 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____53971
              in
           let uu____53974 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____53974 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____54015 = term_to_string head1  in
           let uu____54017 =
             let uu____54019 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____54052  ->
                       match uu____54052 with
                       | (p,wopt,e) ->
                           let uu____54069 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____54072 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____54077 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____54077
                              in
                           let uu____54081 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____54069
                             uu____54072 uu____54081))
                in
             FStar_Util.concat_l "\n\t|" uu____54019  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____54015
             uu____54017
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____54093 = FStar_Options.print_universes ()  in
           if uu____54093
           then
             let uu____54097 = term_to_string t  in
             let uu____54099 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____54097 uu____54099
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____54106 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____54109 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____54111 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____54106 uu____54109
      uu____54111

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_54114  ->
    match uu___434_54114 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____54120 = FStar_Util.string_of_int i  in
        let uu____54122 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____54120 uu____54122
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____54129 = bv_to_string x  in
        let uu____54131 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____54129 uu____54131
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____54140 = bv_to_string x  in
        let uu____54142 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____54140 uu____54142
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____54149 = FStar_Util.string_of_int i  in
        let uu____54151 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____54149 uu____54151
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____54158 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____54158

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____54162 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____54162 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____54178 =
      let uu____54180 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54180  in
    if uu____54178
    then
      let e =
        let uu____54185 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____54185  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____54214 = fv_to_string l  in
           let uu____54216 =
             let uu____54218 =
               FStar_List.map
                 (fun uu____54232  ->
                    match uu____54232 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____54218 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____54214 uu____54216
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____54257) ->
           let uu____54262 = FStar_Options.print_bound_var_types ()  in
           if uu____54262
           then
             let uu____54266 = bv_to_string x1  in
             let uu____54268 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____54266 uu____54268
           else
             (let uu____54273 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____54273)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____54277 = FStar_Options.print_bound_var_types ()  in
           if uu____54277
           then
             let uu____54281 = bv_to_string x1  in
             let uu____54283 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____54281 uu____54283
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____54290 = FStar_Options.print_bound_var_types ()  in
           if uu____54290
           then
             let uu____54294 = bv_to_string x1  in
             let uu____54296 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____54294 uu____54296
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____54305 = quals_to_string' quals  in
      let uu____54307 =
        let uu____54309 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____54329 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____54331 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____54333 =
                    let uu____54335 = FStar_Options.print_universes ()  in
                    if uu____54335
                    then
                      let uu____54339 =
                        let uu____54341 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____54341 ">"  in
                      Prims.op_Hat "<" uu____54339
                    else ""  in
                  let uu____54348 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____54350 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____54329
                    uu____54331 uu____54333 uu____54348 uu____54350))
           in
        FStar_Util.concat_l "\n and " uu____54309  in
      FStar_Util.format3 "%slet %s %s" uu____54305
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____54307

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_54365  ->
    match uu___435_54365 with
    | [] -> ""
    | tms ->
        let uu____54373 =
          let uu____54375 =
            FStar_List.map
              (fun t  ->
                 let uu____54383 = term_to_string t  in paren uu____54383)
              tms
             in
          FStar_All.pipe_right uu____54375 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____54373

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____54392 = FStar_Options.print_effect_args ()  in
    if uu____54392
    then
      let uu____54396 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____54396
    else
      (let uu____54399 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____54401 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____54399 uu____54401)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_54405  ->
      match uu___436_54405 with
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
          let uu____54423 =
            let uu____54425 = term_to_string t  in
            Prims.op_Hat uu____54425 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____54423
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
      let uu____54445 =
        let uu____54447 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____54447  in
      if uu____54445
      then
        let uu____54451 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____54451 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____54462 = b  in
         match uu____54462 with
         | (a,imp) ->
             let uu____54476 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____54476
             then
               let uu____54480 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____54480
             else
               (let uu____54485 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____54488 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____54488)
                   in
                if uu____54485
                then
                  let uu____54492 = nm_to_string a  in
                  imp_to_string uu____54492 imp
                else
                  (let uu____54496 =
                     let uu____54498 = nm_to_string a  in
                     let uu____54500 =
                       let uu____54502 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____54502  in
                     Prims.op_Hat uu____54498 uu____54500  in
                   imp_to_string uu____54496 imp)))

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
        let uu____54521 = FStar_Options.print_implicits ()  in
        if uu____54521 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____54532 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____54532 (FStar_String.concat sep)
      else
        (let uu____54560 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____54560 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_54574  ->
    match uu___437_54574 with
    | (a,imp) ->
        let uu____54588 = term_to_string a  in imp_to_string uu____54588 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____54600 = FStar_Options.print_implicits ()  in
      if uu____54600 then args else filter_imp args  in
    let uu____54615 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____54615 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____54644 = FStar_Options.ugly ()  in
      if uu____54644
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____54655 =
      let uu____54657 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54657  in
    if uu____54655
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
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
                     FStar_Util.format2 "Tot<%s> %s" uu____54689 uu____54691
                 | uu____54694 ->
                     let uu____54697 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____54697))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____54710 =
             let uu____54711 = FStar_Syntax_Subst.compress t  in
             uu____54711.FStar_Syntax_Syntax.n  in
           (match uu____54710 with
            | FStar_Syntax_Syntax.Tm_type uu____54715 when
                let uu____54716 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____54716 -> term_to_string t
            | uu____54718 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____54721 = univ_to_string u  in
                     let uu____54723 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____54721 uu____54723
                 | uu____54726 ->
                     let uu____54729 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____54729))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____54735 = FStar_Options.print_effect_args ()  in
             if uu____54735
             then
               let uu____54739 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____54741 =
                 let uu____54743 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____54743 (FStar_String.concat ", ")
                  in
               let uu____54758 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____54760 =
                 let uu____54762 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____54762 (FStar_String.concat ", ")
                  in
               let uu____54789 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____54739 uu____54741 uu____54758 uu____54760 uu____54789
             else
               (let uu____54794 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_54800  ->
                           match uu___438_54800 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____54803 -> false)))
                    &&
                    (let uu____54806 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____54806)
                   in
                if uu____54794
                then
                  let uu____54810 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____54810
                else
                  (let uu____54815 =
                     ((let uu____54819 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____54819) &&
                        (let uu____54822 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____54822))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____54815
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____54828 =
                        (let uu____54832 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____54832) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_54838  ->
                                   match uu___439_54838 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____54841 -> false)))
                         in
                      if uu____54828
                      then
                        let uu____54845 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____54845
                      else
                        (let uu____54850 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____54852 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____54850 uu____54852))))
              in
           let dec =
             let uu____54857 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_54870  ->
                       match uu___440_54870 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____54877 =
                             let uu____54879 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____54879
                              in
                           [uu____54877]
                       | uu____54884 -> []))
                in
             FStar_All.pipe_right uu____54857 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____54903 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_54913  ->
    match uu___441_54913 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____54930 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____54967 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____54992  ->
                              match uu____54992 with
                              | (t,uu____55001) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____54967
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____54930 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____55018 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____55018
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____55023) ->
        let uu____55028 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____55028
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____55039 = sli m  in
        let uu____55041 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____55039 uu____55041
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____55051 = sli m  in
        let uu____55053 = sli m'  in
        let uu____55055 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____55051
          uu____55053 uu____55055

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____55070 = FStar_Options.ugly ()  in
      if uu____55070
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
      let uu____55091 = b  in
      match uu____55091 with
      | (a,imp) ->
          let n1 =
            let uu____55099 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____55099
            then FStar_Util.JsonNull
            else
              (let uu____55104 =
                 let uu____55106 = nm_to_string a  in
                 imp_to_string uu____55106 imp  in
               FStar_Util.JsonStr uu____55104)
             in
          let t =
            let uu____55109 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____55109  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____55141 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____55141
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____55159 = FStar_Options.print_universes ()  in
    if uu____55159 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____55175 =
      let uu____55177 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____55177  in
    if uu____55175
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____55187 = s  in
       match uu____55187 with
       | (us,t) ->
           let uu____55199 =
             let uu____55201 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____55201  in
           let uu____55205 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____55199 uu____55205)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____55215 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____55217 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____55220 =
      let uu____55222 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____55222  in
    let uu____55226 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____55228 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____55215 uu____55217
      uu____55220 uu____55226 uu____55228
  
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
          let uu____55259 =
            let uu____55261 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____55261  in
          if uu____55259
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____55282 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____55282 (FStar_String.concat ",\n\t")
                in
             let uu____55297 =
               let uu____55301 =
                 let uu____55305 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____55307 =
                   let uu____55311 =
                     let uu____55313 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____55313  in
                   let uu____55317 =
                     let uu____55321 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____55324 =
                       let uu____55328 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____55330 =
                         let uu____55334 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____55336 =
                           let uu____55340 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____55342 =
                             let uu____55346 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____55348 =
                               let uu____55352 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____55354 =
                                 let uu____55358 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____55360 =
                                   let uu____55364 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____55366 =
                                     let uu____55370 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____55372 =
                                       let uu____55376 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____55378 =
                                         let uu____55382 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____55384 =
                                           let uu____55388 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____55390 =
                                             let uu____55394 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____55396 =
                                               let uu____55400 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____55402 =
                                                 let uu____55406 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____55408 =
                                                   let uu____55412 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____55412]  in
                                                 uu____55406 :: uu____55408
                                                  in
                                               uu____55400 :: uu____55402  in
                                             uu____55394 :: uu____55396  in
                                           uu____55388 :: uu____55390  in
                                         uu____55382 :: uu____55384  in
                                       uu____55376 :: uu____55378  in
                                     uu____55370 :: uu____55372  in
                                   uu____55364 :: uu____55366  in
                                 uu____55358 :: uu____55360  in
                               uu____55352 :: uu____55354  in
                             uu____55346 :: uu____55348  in
                           uu____55340 :: uu____55342  in
                         uu____55334 :: uu____55336  in
                       uu____55328 :: uu____55330  in
                     uu____55321 :: uu____55324  in
                   uu____55311 :: uu____55317  in
                 uu____55305 :: uu____55307  in
               (if for_free then "_for_free " else "") :: uu____55301  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____55297)
  
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
          (lid,univs1,tps,k,uu____55486,uu____55487) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____55503 = FStar_Options.print_universes ()  in
          if uu____55503
          then
            let uu____55507 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____55507 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____55516,uu____55517,uu____55518) ->
          let uu____55525 = FStar_Options.print_universes ()  in
          if uu____55525
          then
            let uu____55529 = univ_names_to_string univs1  in
            let uu____55531 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____55529
              lid.FStar_Ident.str uu____55531
          else
            (let uu____55536 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____55536)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____55542 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____55544 =
            let uu____55546 = FStar_Options.print_universes ()  in
            if uu____55546
            then
              let uu____55550 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____55550
            else ""  in
          let uu____55556 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____55542
            lid.FStar_Ident.str uu____55544 uu____55556
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____55562 = FStar_Options.print_universes ()  in
          if uu____55562
          then
            let uu____55566 = univ_names_to_string us  in
            let uu____55568 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____55566 uu____55568
          else
            (let uu____55573 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____55573)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____55577) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____55583 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____55583
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____55587) ->
          let uu____55596 =
            let uu____55598 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____55598 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____55596
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____55643) -> lift_wp
            | (uu____55650,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____55658 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____55658 with
           | (us,t) ->
               let uu____55670 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____55672 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____55674 = univ_names_to_string us  in
               let uu____55676 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____55670
                 uu____55672 uu____55674 uu____55676)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____55688 = FStar_Options.print_universes ()  in
          if uu____55688
          then
            let uu____55692 =
              let uu____55697 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____55697  in
            (match uu____55692 with
             | (univs2,t) ->
                 let uu____55711 =
                   let uu____55716 =
                     let uu____55717 = FStar_Syntax_Subst.compress t  in
                     uu____55717.FStar_Syntax_Syntax.n  in
                   match uu____55716 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____55746 -> failwith "impossible"  in
                 (match uu____55711 with
                  | (tps1,c1) ->
                      let uu____55755 = sli l  in
                      let uu____55757 = univ_names_to_string univs2  in
                      let uu____55759 = binders_to_string " " tps1  in
                      let uu____55762 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____55755
                        uu____55757 uu____55759 uu____55762))
          else
            (let uu____55767 = sli l  in
             let uu____55769 = binders_to_string " " tps  in
             let uu____55772 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____55767 uu____55769
               uu____55772)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____55781 =
            let uu____55783 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____55783  in
          let uu____55793 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____55781 uu____55793
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____55797 ->
        let uu____55800 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____55800 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____55817 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____55817 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____55828,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____55830;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____55832;
                        FStar_Syntax_Syntax.lbdef = uu____55833;
                        FStar_Syntax_Syntax.lbattrs = uu____55834;
                        FStar_Syntax_Syntax.lbpos = uu____55835;_}::[]),uu____55836)
        ->
        let uu____55859 = lbname_to_string lb  in
        let uu____55861 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____55859 uu____55861
    | uu____55864 ->
        let uu____55865 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____55865 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____55889 = sli m.FStar_Syntax_Syntax.name  in
    let uu____55891 =
      let uu____55893 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____55893 (FStar_String.concat "\n")  in
    let uu____55903 =
      let uu____55905 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____55905 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____55889
      uu____55891 uu____55903
  
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
          (let uu____55949 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____55949))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____55958 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____55958)));
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
           (let uu____55999 = f x  in
            FStar_Util.string_builder_append strb uu____55999);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____56008 = f x1  in
                 FStar_Util.string_builder_append strb uu____56008)) xs;
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
           (let uu____56055 = f x  in
            FStar_Util.string_builder_append strb uu____56055);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____56064 = f x1  in
                 FStar_Util.string_builder_append strb uu____56064)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____56086 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____56086
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_56099  ->
    match uu___442_56099 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____56115 =
          let uu____56117 =
            let uu____56119 =
              let uu____56121 =
                let uu____56123 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____56123 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____56121 ")"  in
            Prims.op_Hat " " uu____56119  in
          Prims.op_Hat h uu____56117  in
        Prims.op_Hat "(" uu____56115
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____56138 =
          let uu____56140 = emb_typ_to_string a  in
          let uu____56142 =
            let uu____56144 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____56144  in
          Prims.op_Hat uu____56140 uu____56142  in
        Prims.op_Hat "(" uu____56138
  