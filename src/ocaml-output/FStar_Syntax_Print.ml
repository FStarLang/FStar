open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_51550  ->
    match uu___429_51550 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____51554 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____51554
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____51559 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____51559
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____51563 =
          let uu____51565 = delta_depth_to_string d  in
          Prims.op_Hat uu____51565 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____51563
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____51577 = FStar_Options.print_real_names ()  in
    if uu____51577
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51604 =
      let uu____51606 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____51606  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51604
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51616 = FStar_Options.print_real_names ()  in
    if uu____51616
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____51629 =
      let uu____51631 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____51631  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____51629
  
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
      | uu____51853 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____51866 -> failwith "get_lid"
  
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
  'Auu____51969 'Auu____51970 .
    ('Auu____51969,'Auu____51970) FStar_Util.either -> Prims.bool
  =
  fun uu___430_51980  ->
    match uu___430_51980 with
    | FStar_Util.Inl uu____51985 -> false
    | FStar_Util.Inr uu____51987 -> true
  
let filter_imp :
  'Auu____51994 .
    ('Auu____51994 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____51994 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_52049  ->
            match uu___431_52049 with
            | (uu____52057,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____52064,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____52065)) -> false
            | (uu____52070,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____52071)) -> false
            | uu____52077 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____52095 =
      let uu____52096 = FStar_Syntax_Subst.compress e  in
      uu____52096.FStar_Syntax_Syntax.n  in
    match uu____52095 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____52157 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____52157
        then
          let uu____52166 =
            let uu____52171 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____52171  in
          (match uu____52166 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____52182 =
                 let uu____52185 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____52185 :: xs  in
               FStar_Pervasives_Native.Some uu____52182
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____52197 ->
        let uu____52198 = is_lex_top e  in
        if uu____52198
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____52246 = f hd1  in if uu____52246 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____52278 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____52278
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52309 = get_lid e  in find_lid uu____52309 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____52321 = get_lid e  in find_lid uu____52321 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____52333 = get_lid t  in find_lid uu____52333 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_52347  ->
    match uu___432_52347 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____52358 = FStar_Options.hide_uvar_nums ()  in
    if uu____52358
    then "?"
    else
      (let uu____52365 =
         let uu____52367 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____52367 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____52365)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____52379 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____52381 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____52379 uu____52381
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____52407 = FStar_Options.hide_uvar_nums ()  in
    if uu____52407
    then "?"
    else
      (let uu____52414 =
         let uu____52416 =
           let uu____52418 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____52418 FStar_Util.string_of_int  in
         let uu____52422 =
           let uu____52424 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____52424  in
         Prims.op_Hat uu____52416 uu____52422  in
       Prims.op_Hat "?" uu____52414)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____52452 = FStar_Syntax_Subst.compress_univ u  in
      match uu____52452 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____52465 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____52476 = FStar_Syntax_Subst.compress_univ u  in
    match uu____52476 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____52487 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____52487
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____52494 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____52494
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____52499 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____52499 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____52520 = univ_to_string u2  in
             let uu____52522 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____52520 uu____52522)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____52528 =
          let uu____52530 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____52530 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____52528
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____52549 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____52549 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____52566 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____52566 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_52584  ->
    match uu___433_52584 with
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
        let uu____52600 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____52600
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____52605 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____52605
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____52618 =
          let uu____52620 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52620  in
        let uu____52621 =
          let uu____52623 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52623 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____52618 uu____52621
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____52649 =
          let uu____52651 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____52651  in
        let uu____52652 =
          let uu____52654 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____52654 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____52649
          uu____52652
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____52671 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____52671
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
    | uu____52694 ->
        let uu____52697 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____52697 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____52725 ->
        let uu____52728 = quals_to_string quals  in
        Prims.op_Hat uu____52728 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____52924 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____52924
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____52928 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____52928
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____52932 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____52932
    | FStar_Syntax_Syntax.Tm_uinst uu____52935 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____52943 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____52945 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52947,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____52948;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____52962,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____52963;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____52977 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____52997 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____53013 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____53021 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____53039 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____53063 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____53091 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____53106 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____53120,m) ->
        let uu____53158 = FStar_ST.op_Bang m  in
        (match uu____53158 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____53194 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____53200,m) ->
        let uu____53206 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____53206
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____53210 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____53213 =
      let uu____53215 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____53215  in
    if uu____53213
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____53229 = FStar_Options.print_implicits ()  in
         if uu____53229 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____53237 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____53262,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____53288,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____53290;
             FStar_Syntax_Syntax.rng = uu____53291;_}
           ->
           let uu____53302 =
             let uu____53304 =
               let uu____53306 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____53306  in
             Prims.op_Hat uu____53304 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____53302
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____53312 =
             let uu____53314 =
               let uu____53316 =
                 let uu____53317 =
                   let uu____53326 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____53326  in
                 uu____53317 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____53316  in
             Prims.op_Hat uu____53314 "]"  in
           Prims.op_Hat "[lazy:" uu____53312
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____53395 =
                  match uu____53395 with
                  | (bv,t) ->
                      let uu____53403 = bv_to_string bv  in
                      let uu____53405 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____53403 uu____53405
                   in
                let uu____53408 = term_to_string tm  in
                let uu____53410 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____53408 uu____53410
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____53419 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____53419)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____53442 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____53479 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____53504  ->
                                 match uu____53504 with
                                 | (t1,uu____53513) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____53479
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____53442 (FStar_String.concat "\\/")  in
           let uu____53528 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____53528
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____53542 = tag_of_term t  in
           let uu____53544 = sli m  in
           let uu____53546 = term_to_string t'  in
           let uu____53548 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____53542
             uu____53544 uu____53546 uu____53548
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____53563 = tag_of_term t  in
           let uu____53565 = term_to_string t'  in
           let uu____53567 = sli m0  in
           let uu____53569 = sli m1  in
           let uu____53571 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____53563 uu____53565 uu____53567 uu____53569 uu____53571
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____53586 = FStar_Range.string_of_range r  in
           let uu____53588 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____53586
             uu____53588
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____53597 = lid_to_string l  in
           let uu____53599 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____53601 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____53597
             uu____53599 uu____53601
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____53605) ->
           let uu____53610 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____53610
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____53614 = db_to_string x3  in
           let uu____53616 =
             let uu____53618 =
               let uu____53620 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____53620 ")"  in
             Prims.op_Hat ":(" uu____53618  in
           Prims.op_Hat uu____53614 uu____53616
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____53627)) ->
           let uu____53642 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53642
           then ctx_uvar_to_string u
           else
             (let uu____53648 =
                let uu____53650 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53650  in
              Prims.op_Hat "?" uu____53648)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____53673 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____53673
           then
             let uu____53677 = ctx_uvar_to_string u  in
             let uu____53679 =
               let uu____53681 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____53681 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____53677 uu____53679
           else
             (let uu____53700 =
                let uu____53702 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____53702  in
              Prims.op_Hat "?" uu____53700)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____53709 = FStar_Options.print_universes ()  in
           if uu____53709
           then
             let uu____53713 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____53713
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____53741 = binders_to_string " -> " bs  in
           let uu____53744 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____53741 uu____53744
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____53776 = binders_to_string " " bs  in
                let uu____53779 = term_to_string t2  in
                let uu____53781 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____53790 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____53790)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____53776 uu____53779
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____53781
            | uu____53794 ->
                let uu____53797 = binders_to_string " " bs  in
                let uu____53800 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____53797 uu____53800)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____53809 = bv_to_string xt  in
           let uu____53811 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____53814 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____53809 uu____53811
             uu____53814
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____53846 = term_to_string t  in
           let uu____53848 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____53846 uu____53848
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____53871 = lbs_to_string [] lbs  in
           let uu____53873 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____53871 uu____53873
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____53938 =
                   let uu____53940 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____53940
                     (FStar_Util.dflt "default")
                    in
                 let uu____53951 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____53938 uu____53951
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____53972 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____53972
              in
           let uu____53975 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____53975 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____54016 = term_to_string head1  in
           let uu____54018 =
             let uu____54020 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____54053  ->
                       match uu____54053 with
                       | (p,wopt,e) ->
                           let uu____54070 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____54073 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____54078 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____54078
                              in
                           let uu____54082 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____54070
                             uu____54073 uu____54082))
                in
             FStar_Util.concat_l "\n\t|" uu____54020  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____54016
             uu____54018
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____54094 = FStar_Options.print_universes ()  in
           if uu____54094
           then
             let uu____54098 = term_to_string t  in
             let uu____54100 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____54098 uu____54100
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____54107 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____54110 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____54112 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____54107 uu____54110
      uu____54112

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_54115  ->
    match uu___434_54115 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____54121 = FStar_Util.string_of_int i  in
        let uu____54123 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____54121 uu____54123
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____54130 = bv_to_string x  in
        let uu____54132 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____54130 uu____54132
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____54141 = bv_to_string x  in
        let uu____54143 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____54141 uu____54143
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____54150 = FStar_Util.string_of_int i  in
        let uu____54152 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____54150 uu____54152
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____54159 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____54159

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____54163 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____54163 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____54179 =
      let uu____54181 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54181  in
    if uu____54179
    then
      let e =
        let uu____54186 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____54186  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____54215 = fv_to_string l  in
           let uu____54217 =
             let uu____54219 =
               FStar_List.map
                 (fun uu____54233  ->
                    match uu____54233 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____54219 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____54215 uu____54217
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____54258) ->
           let uu____54263 = FStar_Options.print_bound_var_types ()  in
           if uu____54263
           then
             let uu____54267 = bv_to_string x1  in
             let uu____54269 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____54267 uu____54269
           else
             (let uu____54274 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____54274)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____54278 = FStar_Options.print_bound_var_types ()  in
           if uu____54278
           then
             let uu____54282 = bv_to_string x1  in
             let uu____54284 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____54282 uu____54284
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____54291 = FStar_Options.print_bound_var_types ()  in
           if uu____54291
           then
             let uu____54295 = bv_to_string x1  in
             let uu____54297 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____54295 uu____54297
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____54306 = quals_to_string' quals  in
      let uu____54308 =
        let uu____54310 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____54330 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____54332 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____54334 =
                    let uu____54336 = FStar_Options.print_universes ()  in
                    if uu____54336
                    then
                      let uu____54340 =
                        let uu____54342 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____54342 ">"  in
                      Prims.op_Hat "<" uu____54340
                    else ""  in
                  let uu____54349 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____54351 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____54330
                    uu____54332 uu____54334 uu____54349 uu____54351))
           in
        FStar_Util.concat_l "\n and " uu____54310  in
      FStar_Util.format3 "%slet %s %s" uu____54306
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____54308

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_54366  ->
    match uu___435_54366 with
    | [] -> ""
    | tms ->
        let uu____54374 =
          let uu____54376 =
            FStar_List.map
              (fun t  ->
                 let uu____54384 = term_to_string t  in paren uu____54384)
              tms
             in
          FStar_All.pipe_right uu____54376 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____54374

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____54393 = FStar_Options.print_effect_args ()  in
    if uu____54393
    then
      let uu____54397 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____54397
    else
      (let uu____54400 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____54402 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____54400 uu____54402)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_54406  ->
      match uu___436_54406 with
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
          let uu____54424 =
            let uu____54426 = term_to_string t  in
            Prims.op_Hat uu____54426 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____54424
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
      let uu____54446 =
        let uu____54448 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____54448  in
      if uu____54446
      then
        let uu____54452 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____54452 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____54463 = b  in
         match uu____54463 with
         | (a,imp) ->
             let uu____54477 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____54477
             then
               let uu____54481 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____54481
             else
               (let uu____54486 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____54489 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____54489)
                   in
                if uu____54486
                then
                  let uu____54493 = nm_to_string a  in
                  imp_to_string uu____54493 imp
                else
                  (let uu____54497 =
                     let uu____54499 = nm_to_string a  in
                     let uu____54501 =
                       let uu____54503 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____54503  in
                     Prims.op_Hat uu____54499 uu____54501  in
                   imp_to_string uu____54497 imp)))

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
        let uu____54522 = FStar_Options.print_implicits ()  in
        if uu____54522 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____54533 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____54533 (FStar_String.concat sep)
      else
        (let uu____54561 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____54561 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_54575  ->
    match uu___437_54575 with
    | (a,imp) ->
        let uu____54589 = term_to_string a  in imp_to_string uu____54589 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____54601 = FStar_Options.print_implicits ()  in
      if uu____54601 then args else filter_imp args  in
    let uu____54616 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____54616 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____54645 = FStar_Options.ugly ()  in
      if uu____54645
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____54656 =
      let uu____54658 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____54658  in
    if uu____54656
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____54679 =
             let uu____54680 = FStar_Syntax_Subst.compress t  in
             uu____54680.FStar_Syntax_Syntax.n  in
           (match uu____54679 with
            | FStar_Syntax_Syntax.Tm_type uu____54684 when
                let uu____54685 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____54685 -> term_to_string t
            | uu____54687 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____54690 = univ_to_string u  in
                     let uu____54692 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____54690 uu____54692
                 | uu____54695 ->
                     let uu____54698 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____54698))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____54711 =
             let uu____54712 = FStar_Syntax_Subst.compress t  in
             uu____54712.FStar_Syntax_Syntax.n  in
           (match uu____54711 with
            | FStar_Syntax_Syntax.Tm_type uu____54716 when
                let uu____54717 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____54717 -> term_to_string t
            | uu____54719 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____54722 = univ_to_string u  in
                     let uu____54724 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____54722 uu____54724
                 | uu____54727 ->
                     let uu____54730 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____54730))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____54736 = FStar_Options.print_effect_args ()  in
             if uu____54736
             then
               let uu____54740 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____54742 =
                 let uu____54744 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____54744 (FStar_String.concat ", ")
                  in
               let uu____54759 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____54761 =
                 let uu____54763 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____54763 (FStar_String.concat ", ")
                  in
               let uu____54790 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____54740 uu____54742 uu____54759 uu____54761 uu____54790
             else
               (let uu____54795 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_54801  ->
                           match uu___438_54801 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____54804 -> false)))
                    &&
                    (let uu____54807 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____54807)
                   in
                if uu____54795
                then
                  let uu____54811 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____54811
                else
                  (let uu____54816 =
                     ((let uu____54820 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____54820) &&
                        (let uu____54823 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____54823))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____54816
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____54829 =
                        (let uu____54833 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____54833) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_54839  ->
                                   match uu___439_54839 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____54842 -> false)))
                         in
                      if uu____54829
                      then
                        let uu____54846 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____54846
                      else
                        (let uu____54851 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____54853 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____54851 uu____54853))))
              in
           let dec =
             let uu____54858 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_54871  ->
                       match uu___440_54871 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____54878 =
                             let uu____54880 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____54880
                              in
                           [uu____54878]
                       | uu____54885 -> []))
                in
             FStar_All.pipe_right uu____54858 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____54904 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_54914  ->
    match uu___441_54914 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____54931 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____54968 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____54993  ->
                              match uu____54993 with
                              | (t,uu____55002) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____54968
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____54931 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____55019 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____55019
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____55024) ->
        let uu____55029 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____55029
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____55040 = sli m  in
        let uu____55042 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____55040 uu____55042
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____55052 = sli m  in
        let uu____55054 = sli m'  in
        let uu____55056 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____55052
          uu____55054 uu____55056

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____55071 = FStar_Options.ugly ()  in
      if uu____55071
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
      let uu____55092 = b  in
      match uu____55092 with
      | (a,imp) ->
          let n1 =
            let uu____55100 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____55100
            then FStar_Util.JsonNull
            else
              (let uu____55105 =
                 let uu____55107 = nm_to_string a  in
                 imp_to_string uu____55107 imp  in
               FStar_Util.JsonStr uu____55105)
             in
          let t =
            let uu____55110 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____55110  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____55142 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____55142
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____55160 = FStar_Options.print_universes ()  in
    if uu____55160 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____55176 =
      let uu____55178 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____55178  in
    if uu____55176
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____55188 = s  in
       match uu____55188 with
       | (us,t) ->
           let uu____55200 =
             let uu____55202 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____55202  in
           let uu____55206 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____55200 uu____55206)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____55216 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____55218 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____55221 =
      let uu____55223 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____55223  in
    let uu____55227 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____55229 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____55216 uu____55218
      uu____55221 uu____55227 uu____55229
  
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
          let uu____55260 =
            let uu____55262 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____55262  in
          if uu____55260
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____55283 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____55283 (FStar_String.concat ",\n\t")
                in
             let uu____55298 =
               let uu____55302 =
                 let uu____55306 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____55308 =
                   let uu____55312 =
                     let uu____55314 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____55314  in
                   let uu____55318 =
                     let uu____55322 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____55325 =
                       let uu____55329 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____55331 =
                         let uu____55335 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____55337 =
                           let uu____55341 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____55343 =
                             let uu____55347 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____55349 =
                               let uu____55353 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____55355 =
                                 let uu____55359 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____55361 =
                                   let uu____55365 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____55367 =
                                     let uu____55371 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____55373 =
                                       let uu____55377 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____55379 =
                                         let uu____55383 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____55385 =
                                           let uu____55389 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____55391 =
                                             let uu____55395 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____55397 =
                                               let uu____55401 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____55403 =
                                                 let uu____55407 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____55409 =
                                                   let uu____55413 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____55413]  in
                                                 uu____55407 :: uu____55409
                                                  in
                                               uu____55401 :: uu____55403  in
                                             uu____55395 :: uu____55397  in
                                           uu____55389 :: uu____55391  in
                                         uu____55383 :: uu____55385  in
                                       uu____55377 :: uu____55379  in
                                     uu____55371 :: uu____55373  in
                                   uu____55365 :: uu____55367  in
                                 uu____55359 :: uu____55361  in
                               uu____55353 :: uu____55355  in
                             uu____55347 :: uu____55349  in
                           uu____55341 :: uu____55343  in
                         uu____55335 :: uu____55337  in
                       uu____55329 :: uu____55331  in
                     uu____55322 :: uu____55325  in
                   uu____55312 :: uu____55318  in
                 uu____55306 :: uu____55308  in
               (if for_free then "_for_free " else "") :: uu____55302  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____55298)
  
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
          (lid,univs1,tps,k,uu____55487,uu____55488) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____55504 = FStar_Options.print_universes ()  in
          if uu____55504
          then
            let uu____55508 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____55508 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____55517,uu____55518,uu____55519) ->
          let uu____55526 = FStar_Options.print_universes ()  in
          if uu____55526
          then
            let uu____55530 = univ_names_to_string univs1  in
            let uu____55532 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____55530
              lid.FStar_Ident.str uu____55532
          else
            (let uu____55537 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____55537)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____55543 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____55545 =
            let uu____55547 = FStar_Options.print_universes ()  in
            if uu____55547
            then
              let uu____55551 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____55551
            else ""  in
          let uu____55557 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____55543
            lid.FStar_Ident.str uu____55545 uu____55557
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____55563 = FStar_Options.print_universes ()  in
          if uu____55563
          then
            let uu____55567 = univ_names_to_string us  in
            let uu____55569 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____55567 uu____55569
          else
            (let uu____55574 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____55574)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____55578) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____55584 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____55584
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____55588) ->
          let uu____55597 =
            let uu____55599 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____55599 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____55597
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____55644) -> lift_wp
            | (uu____55651,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____55659 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____55659 with
           | (us,t) ->
               let uu____55671 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____55673 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____55675 = univ_names_to_string us  in
               let uu____55677 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____55671
                 uu____55673 uu____55675 uu____55677)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____55689 = FStar_Options.print_universes ()  in
          if uu____55689
          then
            let uu____55693 =
              let uu____55698 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____55698  in
            (match uu____55693 with
             | (univs2,t) ->
                 let uu____55712 =
                   let uu____55717 =
                     let uu____55718 = FStar_Syntax_Subst.compress t  in
                     uu____55718.FStar_Syntax_Syntax.n  in
                   match uu____55717 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____55747 -> failwith "impossible"  in
                 (match uu____55712 with
                  | (tps1,c1) ->
                      let uu____55756 = sli l  in
                      let uu____55758 = univ_names_to_string univs2  in
                      let uu____55760 = binders_to_string " " tps1  in
                      let uu____55763 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____55756
                        uu____55758 uu____55760 uu____55763))
          else
            (let uu____55768 = sli l  in
             let uu____55770 = binders_to_string " " tps  in
             let uu____55773 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____55768 uu____55770
               uu____55773)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____55782 =
            let uu____55784 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____55784  in
          let uu____55794 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____55782 uu____55794
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____55798 ->
        let uu____55801 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____55801 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____55818 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____55818 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____55829,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____55831;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____55833;
                        FStar_Syntax_Syntax.lbdef = uu____55834;
                        FStar_Syntax_Syntax.lbattrs = uu____55835;
                        FStar_Syntax_Syntax.lbpos = uu____55836;_}::[]),uu____55837)
        ->
        let uu____55860 = lbname_to_string lb  in
        let uu____55862 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____55860 uu____55862
    | uu____55865 ->
        let uu____55866 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____55866 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____55890 = sli m.FStar_Syntax_Syntax.name  in
    let uu____55892 =
      let uu____55894 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____55894 (FStar_String.concat "\n")  in
    let uu____55904 =
      let uu____55906 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____55906 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____55890
      uu____55892 uu____55904
  
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
          (let uu____55950 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____55950))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____55959 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____55959)));
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
           (let uu____56000 = f x  in
            FStar_Util.string_builder_append strb uu____56000);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____56009 = f x1  in
                 FStar_Util.string_builder_append strb uu____56009)) xs;
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
           (let uu____56056 = f x  in
            FStar_Util.string_builder_append strb uu____56056);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____56065 = f x1  in
                 FStar_Util.string_builder_append strb uu____56065)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____56087 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____56087
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_56100  ->
    match uu___442_56100 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____56116 =
          let uu____56118 =
            let uu____56120 =
              let uu____56122 =
                let uu____56124 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____56124 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____56122 ")"  in
            Prims.op_Hat " " uu____56120  in
          Prims.op_Hat h uu____56118  in
        Prims.op_Hat "(" uu____56116
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____56139 =
          let uu____56141 = emb_typ_to_string a  in
          let uu____56143 =
            let uu____56145 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____56145  in
          Prims.op_Hat uu____56141 uu____56143  in
        Prims.op_Hat "(" uu____56139
  