open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_51516  ->
    match uu___429_51516 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____51520 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____51520
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____51525 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____51525
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____51529 =
          let uu____51531 = delta_depth_to_string d  in
          Prims.op_Hat uu____51531 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____51529
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____51543 = FStar_Options.print_real_names ()  in
    if uu____51543
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51570 =
      let uu____51572 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____51572  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51570
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51582 = FStar_Options.print_real_names ()  in
    if uu____51582
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51595 =
      let uu____51597 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____51597  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51595
  
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
      | uu____51819 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____51832 -> failwith "get_lid"
  
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
  'Auu____51935 'Auu____51936 .
    ('Auu____51935,'Auu____51936) FStar_Util.either -> Prims.bool
  =
  fun uu___430_51946  ->
    match uu___430_51946 with
    | FStar_Util.Inl uu____51951 -> false
    | FStar_Util.Inr uu____51953 -> true
  
let filter_imp :
  'Auu____51960 .
    ('Auu____51960 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51960 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_52015  ->
            match uu___431_52015 with
            | (uu____52023,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____52030,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____52031)) -> false
            | (uu____52036,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____52037)) -> false
            | uu____52043 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____52061 =
      let uu____52062 = FStar_Syntax_Subst.compress e  in
      uu____52062.FStar_Syntax_Syntax.n  in
    match uu____52061 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____52123 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____52123
        then
          let uu____52132 =
            let uu____52137 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____52137  in
          (match uu____52132 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____52148 =
                 let uu____52151 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____52151 :: xs  in
               FStar_Pervasives_Native.Some uu____52148
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____52163 ->
        let uu____52164 = is_lex_top e  in
        if uu____52164
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____52212 = f hd1  in if uu____52212 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____52244 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____52244
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52275 = get_lid e  in find_lid uu____52275 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52287 = get_lid e  in find_lid uu____52287 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____52299 = get_lid t  in find_lid uu____52299 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_52313  ->
    match uu___432_52313 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____52324 = FStar_Options.hide_uvar_nums ()  in
    if uu____52324
    then "?"
    else
      (let uu____52331 =
         let uu____52333 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____52333 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____52331)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____52345 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____52347 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____52345 uu____52347
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____52373 = FStar_Options.hide_uvar_nums ()  in
    if uu____52373
    then "?"
    else
      (let uu____52380 =
         let uu____52382 =
           let uu____52384 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____52384 FStar_Util.string_of_int  in
         let uu____52388 =
           let uu____52390 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____52390  in
         Prims.op_Hat uu____52382 uu____52388  in
       Prims.op_Hat "?" uu____52380)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____52418 = FStar_Syntax_Subst.compress_univ u  in
      match uu____52418 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____52431 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____52442 = FStar_Syntax_Subst.compress_univ u  in
    match uu____52442 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____52453 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____52453
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____52460 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____52460
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____52465 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____52465 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____52486 = univ_to_string u2  in
             let uu____52488 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____52486 uu____52488)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____52494 =
          let uu____52496 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____52496 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____52494
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____52515 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____52515 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____52532 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____52532 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_52550  ->
    match uu___433_52550 with
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
        let uu____52566 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____52566
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____52571 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____52571
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____52584 =
          let uu____52586 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52586  in
        let uu____52587 =
          let uu____52589 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52589 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____52584 uu____52587
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____52615 =
          let uu____52617 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52617  in
        let uu____52618 =
          let uu____52620 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52620 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____52615
          uu____52618
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____52637 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____52637
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
    | uu____52660 ->
        let uu____52663 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____52663 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____52691 ->
        let uu____52694 = quals_to_string quals  in
        Prims.op_Hat uu____52694 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____52890 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____52890
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____52894 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____52894
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____52898 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____52898
    | FStar_Syntax_Syntax.Tm_uinst uu____52901 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____52909 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____52911 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52913,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____52914;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52928,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____52929;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____52943 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____52963 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____52979 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____52987 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____53005 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____53029 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____53057 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____53072 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____53086,m) ->
        let uu____53124 = FStar_ST.op_Bang m  in
        (match uu____53124 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____53160 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____53166,m) ->
        let uu____53172 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____53172
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____53176 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____53179 =
      let uu____53181 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____53181  in
    if uu____53179
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____53195 = FStar_Options.print_implicits ()  in
         if uu____53195 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____53203 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____53228,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____53254,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____53256;
             FStar_Syntax_Syntax.rng = uu____53257;_}
           ->
           let uu____53268 =
             let uu____53270 =
               let uu____53272 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____53272  in
             Prims.op_Hat uu____53270 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____53268
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____53278 =
             let uu____53280 =
               let uu____53282 =
                 let uu____53283 =
                   let uu____53292 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____53292  in
                 uu____53283 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____53282  in
             Prims.op_Hat uu____53280 "]"  in
           Prims.op_Hat "[lazy:" uu____53278
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____53361 =
                  match uu____53361 with
                  | (bv,t) ->
                      let uu____53369 = bv_to_string bv  in
                      let uu____53371 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____53369 uu____53371
                   in
                let uu____53374 = term_to_string tm  in
                let uu____53376 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____53374 uu____53376
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____53385 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____53385)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____53408 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____53445 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____53470  ->
                                 match uu____53470 with
                                 | (t1,uu____53479) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____53445
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____53408 (FStar_String.concat "\\/")  in
           let uu____53494 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____53494
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____53508 = tag_of_term t  in
           let uu____53510 = sli m  in
           let uu____53512 = term_to_string t'  in
           let uu____53514 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____53508
             uu____53510 uu____53512 uu____53514
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____53529 = tag_of_term t  in
           let uu____53531 = term_to_string t'  in
           let uu____53533 = sli m0  in
           let uu____53535 = sli m1  in
           let uu____53537 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____53529 uu____53531 uu____53533 uu____53535 uu____53537
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____53552 = FStar_Range.string_of_range r  in
           let uu____53554 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____53552
             uu____53554
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____53563 = lid_to_string l  in
           let uu____53565 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____53567 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____53563
             uu____53565 uu____53567
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____53571) ->
           let uu____53576 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____53576
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____53580 = db_to_string x3  in
           let uu____53582 =
             let uu____53584 =
               let uu____53586 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____53586 ")"  in
             Prims.op_Hat ":(" uu____53584  in
           Prims.op_Hat uu____53580 uu____53582
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____53593)) ->
           let uu____53608 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53608
           then ctx_uvar_to_string u
           else
             (let uu____53614 =
                let uu____53616 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53616  in
              Prims.op_Hat "?" uu____53614)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____53639 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53639
           then
             let uu____53643 = ctx_uvar_to_string u  in
             let uu____53645 =
               let uu____53647 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____53647 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____53643 uu____53645
           else
             (let uu____53666 =
                let uu____53668 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53668  in
              Prims.op_Hat "?" uu____53666)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____53675 = FStar_Options.print_universes ()  in
           if uu____53675
           then
             let uu____53679 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____53679
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____53707 = binders_to_string " -> " bs  in
           let uu____53710 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____53707 uu____53710
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____53742 = binders_to_string " " bs  in
                let uu____53745 = term_to_string t2  in
                let uu____53747 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____53756 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____53756)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____53742 uu____53745
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____53747
            | uu____53760 ->
                let uu____53763 = binders_to_string " " bs  in
                let uu____53766 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____53763 uu____53766)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____53775 = bv_to_string xt  in
           let uu____53777 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____53780 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____53775 uu____53777
             uu____53780
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____53812 = term_to_string t  in
           let uu____53814 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____53812 uu____53814
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____53837 = lbs_to_string [] lbs  in
           let uu____53839 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____53837 uu____53839
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____53904 =
                   let uu____53906 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____53906
                     (FStar_Util.dflt "default")
                    in
                 let uu____53917 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____53904 uu____53917
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____53938 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____53938
              in
           let uu____53941 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____53941 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____53982 = term_to_string head1  in
           let uu____53984 =
             let uu____53986 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____54019  ->
                       match uu____54019 with
                       | (p,wopt,e) ->
                           let uu____54036 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____54039 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____54044 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____54044
                              in
                           let uu____54048 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____54036
                             uu____54039 uu____54048))
                in
             FStar_Util.concat_l "\n\t|" uu____53986  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____53982
             uu____53984
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____54060 = FStar_Options.print_universes ()  in
           if uu____54060
           then
             let uu____54064 = term_to_string t  in
             let uu____54066 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____54064 uu____54066
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____54073 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____54076 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____54078 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____54073 uu____54076
      uu____54078

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_54081  ->
    match uu___434_54081 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____54087 = FStar_Util.string_of_int i  in
        let uu____54089 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____54087 uu____54089
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____54096 = bv_to_string x  in
        let uu____54098 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____54096 uu____54098
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____54107 = bv_to_string x  in
        let uu____54109 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____54107 uu____54109
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____54116 = FStar_Util.string_of_int i  in
        let uu____54118 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____54116 uu____54118
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____54125 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____54125

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____54129 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____54129 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____54145 =
      let uu____54147 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54147  in
    if uu____54145
    then
      let e =
        let uu____54152 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____54152  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____54181 = fv_to_string l  in
           let uu____54183 =
             let uu____54185 =
               FStar_List.map
                 (fun uu____54199  ->
                    match uu____54199 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____54185 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____54181 uu____54183
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____54224) ->
           let uu____54229 = FStar_Options.print_bound_var_types ()  in
           if uu____54229
           then
             let uu____54233 = bv_to_string x1  in
             let uu____54235 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____54233 uu____54235
           else
             (let uu____54240 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____54240)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____54244 = FStar_Options.print_bound_var_types ()  in
           if uu____54244
           then
             let uu____54248 = bv_to_string x1  in
             let uu____54250 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____54248 uu____54250
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____54257 = FStar_Options.print_bound_var_types ()  in
           if uu____54257
           then
             let uu____54261 = bv_to_string x1  in
             let uu____54263 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____54261 uu____54263
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____54272 = quals_to_string' quals  in
      let uu____54274 =
        let uu____54276 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____54296 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____54298 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____54300 =
                    let uu____54302 = FStar_Options.print_universes ()  in
                    if uu____54302
                    then
                      let uu____54306 =
                        let uu____54308 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____54308 ">"  in
                      Prims.op_Hat "<" uu____54306
                    else ""  in
                  let uu____54315 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____54317 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____54296
                    uu____54298 uu____54300 uu____54315 uu____54317))
           in
        FStar_Util.concat_l "\n and " uu____54276  in
      FStar_Util.format3 "%slet %s %s" uu____54272
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____54274

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_54332  ->
    match uu___435_54332 with
    | [] -> ""
    | tms ->
        let uu____54340 =
          let uu____54342 =
            FStar_List.map
              (fun t  ->
                 let uu____54350 = term_to_string t  in paren uu____54350)
              tms
             in
          FStar_All.pipe_right uu____54342 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____54340

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____54359 = FStar_Options.print_effect_args ()  in
    if uu____54359
    then
      let uu____54363 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____54363
    else
      (let uu____54366 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____54368 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____54366 uu____54368)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_54372  ->
      match uu___436_54372 with
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
          let uu____54390 =
            let uu____54392 = term_to_string t  in
            Prims.op_Hat uu____54392 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____54390
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
      let uu____54412 =
        let uu____54414 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____54414  in
      if uu____54412
      then
        let uu____54418 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____54418 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____54429 = b  in
         match uu____54429 with
         | (a,imp) ->
             let uu____54443 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____54443
             then
               let uu____54447 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____54447
             else
               (let uu____54452 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____54455 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____54455)
                   in
                if uu____54452
                then
                  let uu____54459 = nm_to_string a  in
                  imp_to_string uu____54459 imp
                else
                  (let uu____54463 =
                     let uu____54465 = nm_to_string a  in
                     let uu____54467 =
                       let uu____54469 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____54469  in
                     Prims.op_Hat uu____54465 uu____54467  in
                   imp_to_string uu____54463 imp)))

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
        let uu____54488 = FStar_Options.print_implicits ()  in
        if uu____54488 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____54499 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____54499 (FStar_String.concat sep)
      else
        (let uu____54527 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____54527 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_54541  ->
    match uu___437_54541 with
    | (a,imp) ->
        let uu____54555 = term_to_string a  in imp_to_string uu____54555 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____54567 = FStar_Options.print_implicits ()  in
      if uu____54567 then args else filter_imp args  in
    let uu____54582 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____54582 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____54611 = FStar_Options.ugly ()  in
      if uu____54611
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____54622 =
      let uu____54624 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54624  in
    if uu____54622
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____54645 =
             let uu____54646 = FStar_Syntax_Subst.compress t  in
             uu____54646.FStar_Syntax_Syntax.n  in
           (match uu____54645 with
            | FStar_Syntax_Syntax.Tm_type uu____54650 when
                let uu____54651 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____54651 -> term_to_string t
            | uu____54653 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____54656 = univ_to_string u  in
                     let uu____54658 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____54656 uu____54658
                 | uu____54661 ->
                     let uu____54664 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____54664))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____54677 =
             let uu____54678 = FStar_Syntax_Subst.compress t  in
             uu____54678.FStar_Syntax_Syntax.n  in
           (match uu____54677 with
            | FStar_Syntax_Syntax.Tm_type uu____54682 when
                let uu____54683 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____54683 -> term_to_string t
            | uu____54685 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____54688 = univ_to_string u  in
                     let uu____54690 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____54688 uu____54690
                 | uu____54693 ->
                     let uu____54696 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____54696))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____54702 = FStar_Options.print_effect_args ()  in
             if uu____54702
             then
               let uu____54706 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____54708 =
                 let uu____54710 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____54710 (FStar_String.concat ", ")
                  in
               let uu____54725 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____54727 =
                 let uu____54729 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____54729 (FStar_String.concat ", ")
                  in
               let uu____54756 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____54706 uu____54708 uu____54725 uu____54727 uu____54756
             else
               (let uu____54761 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_54767  ->
                           match uu___438_54767 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____54770 -> false)))
                    &&
                    (let uu____54773 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____54773)
                   in
                if uu____54761
                then
                  let uu____54777 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____54777
                else
                  (let uu____54782 =
                     ((let uu____54786 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____54786) &&
                        (let uu____54789 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____54789))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____54782
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____54795 =
                        (let uu____54799 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____54799) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_54805  ->
                                   match uu___439_54805 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____54808 -> false)))
                         in
                      if uu____54795
                      then
                        let uu____54812 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____54812
                      else
                        (let uu____54817 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____54819 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____54817 uu____54819))))
              in
           let dec =
             let uu____54824 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_54837  ->
                       match uu___440_54837 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____54844 =
                             let uu____54846 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____54846
                              in
                           [uu____54844]
                       | uu____54851 -> []))
                in
             FStar_All.pipe_right uu____54824 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____54870 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_54880  ->
    match uu___441_54880 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____54897 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____54934 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____54959  ->
                              match uu____54959 with
                              | (t,uu____54968) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____54934
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____54897 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____54985 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____54985
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____54990) ->
        let uu____54995 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____54995
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____55006 = sli m  in
        let uu____55008 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____55006 uu____55008
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____55018 = sli m  in
        let uu____55020 = sli m'  in
        let uu____55022 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____55018
          uu____55020 uu____55022

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____55037 = FStar_Options.ugly ()  in
      if uu____55037
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
      let uu____55058 = b  in
      match uu____55058 with
      | (a,imp) ->
          let n1 =
            let uu____55066 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____55066
            then FStar_Util.JsonNull
            else
              (let uu____55071 =
                 let uu____55073 = nm_to_string a  in
                 imp_to_string uu____55073 imp  in
               FStar_Util.JsonStr uu____55071)
             in
          let t =
            let uu____55076 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____55076  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____55108 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____55108
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____55126 = FStar_Options.print_universes ()  in
    if uu____55126 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____55142 =
      let uu____55144 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____55144  in
    if uu____55142
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____55154 = s  in
       match uu____55154 with
       | (us,t) ->
           let uu____55166 =
             let uu____55168 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____55168  in
           let uu____55172 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____55166 uu____55172)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____55182 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____55184 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____55187 =
      let uu____55189 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____55189  in
    let uu____55193 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____55195 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____55182 uu____55184
      uu____55187 uu____55193 uu____55195
  
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
          let uu____55226 =
            let uu____55228 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____55228  in
          if uu____55226
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____55249 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____55249 (FStar_String.concat ",\n\t")
                in
             let uu____55264 =
               let uu____55268 =
                 let uu____55272 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____55274 =
                   let uu____55278 =
                     let uu____55280 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____55280  in
                   let uu____55284 =
                     let uu____55288 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____55291 =
                       let uu____55295 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____55297 =
                         let uu____55301 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____55303 =
                           let uu____55307 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____55309 =
                             let uu____55313 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____55315 =
                               let uu____55319 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____55321 =
                                 let uu____55325 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____55327 =
                                   let uu____55331 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____55333 =
                                     let uu____55337 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____55339 =
                                       let uu____55343 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____55345 =
                                         let uu____55349 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____55351 =
                                           let uu____55355 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____55357 =
                                             let uu____55361 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____55363 =
                                               let uu____55367 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____55369 =
                                                 let uu____55373 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____55375 =
                                                   let uu____55379 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____55379]  in
                                                 uu____55373 :: uu____55375
                                                  in
                                               uu____55367 :: uu____55369  in
                                             uu____55361 :: uu____55363  in
                                           uu____55355 :: uu____55357  in
                                         uu____55349 :: uu____55351  in
                                       uu____55343 :: uu____55345  in
                                     uu____55337 :: uu____55339  in
                                   uu____55331 :: uu____55333  in
                                 uu____55325 :: uu____55327  in
                               uu____55319 :: uu____55321  in
                             uu____55313 :: uu____55315  in
                           uu____55307 :: uu____55309  in
                         uu____55301 :: uu____55303  in
                       uu____55295 :: uu____55297  in
                     uu____55288 :: uu____55291  in
                   uu____55278 :: uu____55284  in
                 uu____55272 :: uu____55274  in
               (if for_free then "_for_free " else "") :: uu____55268  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____55264)
  
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
          (lid,univs1,tps,k,uu____55453,uu____55454) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____55470 = FStar_Options.print_universes ()  in
          if uu____55470
          then
            let uu____55474 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____55474 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____55483,uu____55484,uu____55485) ->
          let uu____55492 = FStar_Options.print_universes ()  in
          if uu____55492
          then
            let uu____55496 = univ_names_to_string univs1  in
            let uu____55498 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____55496
              lid.FStar_Ident.str uu____55498
          else
            (let uu____55503 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____55503)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____55509 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____55511 =
            let uu____55513 = FStar_Options.print_universes ()  in
            if uu____55513
            then
              let uu____55517 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____55517
            else ""  in
          let uu____55523 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____55509
            lid.FStar_Ident.str uu____55511 uu____55523
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____55529 = FStar_Options.print_universes ()  in
          if uu____55529
          then
            let uu____55533 = univ_names_to_string us  in
            let uu____55535 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____55533 uu____55535
          else
            (let uu____55540 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____55540)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____55544) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____55550 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____55550
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____55554) ->
          let uu____55563 =
            let uu____55565 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____55565 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____55563
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____55610) -> lift_wp
            | (uu____55617,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____55625 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____55625 with
           | (us,t) ->
               let uu____55637 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____55639 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____55641 = univ_names_to_string us  in
               let uu____55643 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____55637
                 uu____55639 uu____55641 uu____55643)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____55655 = FStar_Options.print_universes ()  in
          if uu____55655
          then
            let uu____55659 =
              let uu____55664 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____55664  in
            (match uu____55659 with
             | (univs2,t) ->
                 let uu____55678 =
                   let uu____55683 =
                     let uu____55684 = FStar_Syntax_Subst.compress t  in
                     uu____55684.FStar_Syntax_Syntax.n  in
                   match uu____55683 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____55713 -> failwith "impossible"  in
                 (match uu____55678 with
                  | (tps1,c1) ->
                      let uu____55722 = sli l  in
                      let uu____55724 = univ_names_to_string univs2  in
                      let uu____55726 = binders_to_string " " tps1  in
                      let uu____55729 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____55722
                        uu____55724 uu____55726 uu____55729))
          else
            (let uu____55734 = sli l  in
             let uu____55736 = binders_to_string " " tps  in
             let uu____55739 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____55734 uu____55736
               uu____55739)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____55748 =
            let uu____55750 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____55750  in
          let uu____55760 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____55748 uu____55760
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____55764 ->
        let uu____55767 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____55767 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____55784 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____55784 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____55795,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____55797;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____55799;
                        FStar_Syntax_Syntax.lbdef = uu____55800;
                        FStar_Syntax_Syntax.lbattrs = uu____55801;
                        FStar_Syntax_Syntax.lbpos = uu____55802;_}::[]),uu____55803)
        ->
        let uu____55826 = lbname_to_string lb  in
        let uu____55828 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____55826 uu____55828
    | uu____55831 ->
        let uu____55832 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____55832 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____55856 = sli m.FStar_Syntax_Syntax.name  in
    let uu____55858 =
      let uu____55860 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____55860 (FStar_String.concat "\n")  in
    let uu____55870 =
      let uu____55872 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____55872 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____55856
      uu____55858 uu____55870
  
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
          (let uu____55916 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____55916))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____55925 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____55925)));
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
           (let uu____55966 = f x  in
            FStar_Util.string_builder_append strb uu____55966);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____55975 = f x1  in
                 FStar_Util.string_builder_append strb uu____55975)) xs;
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
           (let uu____56022 = f x  in
            FStar_Util.string_builder_append strb uu____56022);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____56031 = f x1  in
                 FStar_Util.string_builder_append strb uu____56031)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____56053 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____56053
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_56066  ->
    match uu___442_56066 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____56082 =
          let uu____56084 =
            let uu____56086 =
              let uu____56088 =
                let uu____56090 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____56090 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____56088 ")"  in
            Prims.op_Hat " " uu____56086  in
          Prims.op_Hat h uu____56084  in
        Prims.op_Hat "(" uu____56082
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____56105 =
          let uu____56107 = emb_typ_to_string a  in
          let uu____56109 =
            let uu____56111 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____56111  in
          Prims.op_Hat uu____56107 uu____56109  in
        Prims.op_Hat "(" uu____56105
  