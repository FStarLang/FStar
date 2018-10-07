open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___213_5  ->
    match uu___213_5 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____7 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_constant_at_level " uu____7
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____9 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_equational_at_level " uu____9
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____11 =
          let uu____12 = delta_depth_to_string d  in
          Prims.strcat uu____12 ")"  in
        Prims.strcat "Delta_abstract (" uu____11
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____18 = FStar_Options.print_real_names ()  in
    if uu____18
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____35 =
      let uu____36 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____36  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____35
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____42 = FStar_Options.print_real_names ()  in
    if uu____42
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____49 =
      let uu____50 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____50  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____49
  
let (infix_prim_ops :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
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
let (unary_prim_ops :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
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
      | uu____188 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____199 -> failwith "get_lid"
  
let (is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
  
let (is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
  
let (quants :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list)
  =
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
  'Auu____271 'Auu____272 .
    ('Auu____271,'Auu____272) FStar_Util.either -> Prims.bool
  =
  fun uu___214_281  ->
    match uu___214_281 with
    | FStar_Util.Inl uu____286 -> false
    | FStar_Util.Inr uu____287 -> true
  
let filter_imp :
  'Auu____292 .
    ('Auu____292,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____292,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___215_347  ->
            match uu___215_347 with
            | (uu____354,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____360,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____361)) -> false
            | (uu____364,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____365)) -> false
            | uu____370 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____386 =
      let uu____387 = FStar_Syntax_Subst.compress e  in
      uu____387.FStar_Syntax_Syntax.n  in
    match uu____386 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____448 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____448
        then
          let uu____453 =
            let uu____458 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____458  in
          (match uu____453 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____468 =
                 let uu____471 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____471 :: xs  in
               FStar_Pervasives_Native.Some uu____468
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____481 ->
        let uu____482 = is_lex_top e  in
        if uu____482
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____523 = f hd1  in if uu____523 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____547 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____547
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____571 = get_lid e  in find_lid uu____571 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____581 = get_lid e  in find_lid uu____581 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____591 = get_lid t  in find_lid uu____591 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___216_601  ->
    match uu___216_601 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____609 = FStar_Options.hide_uvar_nums ()  in
    if uu____609
    then "?"
    else
      (let uu____611 =
         let uu____612 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____612 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____611)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____618 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____619 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____618 uu____619
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
     FStar_Unionfind.p_uvar,FStar_Syntax_Syntax.version)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun u  ->
    let uu____641 = FStar_Options.hide_uvar_nums ()  in
    if uu____641
    then "?"
    else
      (let uu____643 =
         let uu____644 =
           let uu____645 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____645 FStar_Util.string_of_int  in
         let uu____646 =
           let uu____647 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____647  in
         Prims.strcat uu____644 uu____646  in
       Prims.strcat "?" uu____643)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____668 = FStar_Syntax_Subst.compress_univ u  in
      match uu____668 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____678 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____686 = FStar_Syntax_Subst.compress_univ u  in
    match uu____686 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____696 = univ_uvar_to_string u1  in
        Prims.strcat "U_unif " uu____696
    | FStar_Syntax_Syntax.U_name x ->
        Prims.strcat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____699 = FStar_Util.string_of_int x  in
        Prims.strcat "@" uu____699
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____701 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____701 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____715 = univ_to_string u2  in
             let uu____716 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____715 uu____716)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____720 =
          let uu____721 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____721 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____720
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____731 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____731 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____741 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____741 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___217_752  ->
    match uu___217_752 with
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
        let uu____754 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____754
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____757 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____757 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____768 =
          let uu____769 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____769  in
        let uu____770 =
          let uu____771 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____771 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____768 uu____770
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____790 =
          let uu____791 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____791  in
        let uu____792 =
          let uu____793 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____793 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____790 uu____792
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____803 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____803
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
    | uu____814 ->
        let uu____817 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____817 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____835 ->
        let uu____838 = quals_to_string quals  in Prims.strcat uu____838 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1002 = db_to_string x  in
        Prims.strcat "Tm_bvar: " uu____1002
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1004 = nm_to_string x  in
        Prims.strcat "Tm_name: " uu____1004
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1006 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____1006
    | FStar_Syntax_Syntax.Tm_uinst uu____1007 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1014 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1015 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1016,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1017;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1030,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1031;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1044 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1063 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1078 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1085 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1102 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1125 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1152 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1165 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1178,m) ->
        let uu____1216 = FStar_ST.op_Bang m  in
        (match uu____1216 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1272 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1277,m) ->
        let uu____1283 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1283
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1284 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1286 =
      let uu____1287 = FStar_Options.ugly ()  in Prims.op_Negation uu____1287
       in
    if uu____1286
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1295 = FStar_Options.print_implicits ()  in
         if uu____1295 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1299 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1322,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1346,thunk);
             FStar_Syntax_Syntax.ltyp = uu____1348;
             FStar_Syntax_Syntax.rng = uu____1349;_}
           ->
           let uu____1360 =
             let uu____1361 =
               let uu____1362 = FStar_Common.force_thunk thunk  in
               term_to_string uu____1362  in
             Prims.strcat uu____1361 "]"  in
           Prims.strcat "[LAZYEMB:" uu____1360
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1406 =
             let uu____1407 =
               let uu____1408 =
                 let uu____1409 =
                   let uu____1418 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1418  in
                 uu____1409 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1408  in
             Prims.strcat uu____1407 "]"  in
           Prims.strcat "[lazy:" uu____1406
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1483 =
                  match uu____1483 with
                  | (bv,t) ->
                      let uu____1490 = bv_to_string bv  in
                      let uu____1491 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1490 uu____1491
                   in
                let uu____1492 = term_to_string tm  in
                let uu____1493 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1492 uu____1493
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1500 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1500)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1520 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1554 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1576  ->
                                 match uu____1576 with
                                 | (t1,uu____1584) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1554
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1520 (FStar_String.concat "\\/")  in
           let uu____1593 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1593
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1605 = tag_of_term t  in
           let uu____1606 = sli m  in
           let uu____1607 = term_to_string t'  in
           let uu____1608 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1605 uu____1606
             uu____1607 uu____1608
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1621 = tag_of_term t  in
           let uu____1622 = term_to_string t'  in
           let uu____1623 = sli m0  in
           let uu____1624 = sli m1  in
           let uu____1625 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1621
             uu____1622 uu____1623 uu____1624 uu____1625
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1634 = FStar_Range.string_of_range r  in
           let uu____1635 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1634
             uu____1635
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1642 = lid_to_string l  in
           let uu____1643 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1644 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1642 uu____1643
             uu____1644
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1646) ->
           let uu____1651 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1651
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1653 = db_to_string x3  in
           let uu____1654 =
             let uu____1655 =
               let uu____1656 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1656 ")"  in
             Prims.strcat ":(" uu____1655  in
           Prims.strcat uu____1653 uu____1654
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____1660)) ->
           let uu____1675 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1675
           then ctx_uvar_to_string u
           else
             (let uu____1677 =
                let uu____1678 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1678  in
              Prims.strcat "?" uu____1677)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____1697 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____1697
           then
             let uu____1698 = ctx_uvar_to_string u  in
             let uu____1699 =
               let uu____1700 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____1700 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____1698 uu____1699
           else
             (let uu____1712 =
                let uu____1713 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____1713  in
              Prims.strcat "?" uu____1712)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1716 = FStar_Options.print_universes ()  in
           if uu____1716
           then
             let uu____1717 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1717
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1741 = binders_to_string " -> " bs  in
           let uu____1742 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1741 uu____1742
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1771 = binders_to_string " " bs  in
                let uu____1772 = term_to_string t2  in
                let uu____1773 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1777 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1777)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1771 uu____1772
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1773
            | uu____1780 ->
                let uu____1783 = binders_to_string " " bs  in
                let uu____1784 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1783 uu____1784)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1791 = bv_to_string xt  in
           let uu____1792 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1793 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1791 uu____1792 uu____1793
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1822 = term_to_string t  in
           let uu____1823 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1822 uu____1823
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1842 = lbs_to_string [] lbs  in
           let uu____1843 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1842 uu____1843
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1904 =
                   let uu____1905 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1905
                     (FStar_Util.dflt "default")
                    in
                 let uu____1910 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1904 uu____1910
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1926 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1926
              in
           let uu____1927 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1927 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1966 = term_to_string head1  in
           let uu____1967 =
             let uu____1968 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1998  ->
                       match uu____1998 with
                       | (p,wopt,e) ->
                           let uu____2014 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____2015 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____2017 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____2017
                              in
                           let uu____2018 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____2014
                             uu____2015 uu____2018))
                in
             FStar_Util.concat_l "\n\t|" uu____1968  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1966 uu____1967
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2025 = FStar_Options.print_universes ()  in
           if uu____2025
           then
             let uu____2026 = term_to_string t  in
             let uu____2027 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2026 uu____2027
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2030 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2031 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2032 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2030 uu____2031
      uu____2032

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___218_2033  ->
    match uu___218_2033 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2036 = FStar_Util.string_of_int i  in
        let uu____2037 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2036 uu____2037
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2040 = bv_to_string x  in
        let uu____2041 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2040 uu____2041
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2048 = bv_to_string x  in
        let uu____2049 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2048 uu____2049
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2052 = FStar_Util.string_of_int i  in
        let uu____2053 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2052 uu____2053
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2056 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2056

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2058 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2058 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2068 =
      let uu____2069 = FStar_Options.ugly ()  in Prims.op_Negation uu____2069
       in
    if uu____2068
    then
      let e =
        let uu____2071 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2071  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2094 = fv_to_string l  in
           let uu____2095 =
             let uu____2096 =
               FStar_List.map
                 (fun uu____2107  ->
                    match uu____2107 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2096 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2094 uu____2095
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2119) ->
           let uu____2124 = FStar_Options.print_bound_var_types ()  in
           if uu____2124
           then
             let uu____2125 = bv_to_string x1  in
             let uu____2126 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2125 uu____2126
           else
             (let uu____2128 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2128)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2130 = FStar_Options.print_bound_var_types ()  in
           if uu____2130
           then
             let uu____2131 = bv_to_string x1  in
             let uu____2132 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2131 uu____2132
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2136 = FStar_Options.print_bound_var_types ()  in
           if uu____2136
           then
             let uu____2137 = bv_to_string x1  in
             let uu____2138 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2137 uu____2138
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2150 = quals_to_string' quals  in
      let uu____2151 =
        let uu____2152 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2168 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2169 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2170 =
                    let uu____2171 = FStar_Options.print_universes ()  in
                    if uu____2171
                    then
                      let uu____2172 =
                        let uu____2173 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2173 ">"  in
                      Prims.strcat "<" uu____2172
                    else ""  in
                  let uu____2175 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2176 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2168
                    uu____2169 uu____2170 uu____2175 uu____2176))
           in
        FStar_Util.concat_l "\n and " uu____2152  in
      FStar_Util.format3 "%slet %s %s" uu____2150
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2151

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___219_2180  ->
    match uu___219_2180 with
    | [] -> ""
    | tms ->
        let uu____2186 =
          let uu____2187 =
            FStar_List.map
              (fun t  ->
                 let uu____2193 = term_to_string t  in paren uu____2193) tms
             in
          FStar_All.pipe_right uu____2187 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2186

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2197 = FStar_Options.print_effect_args ()  in
    if uu____2197
    then
      let uu____2198 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2198
    else
      (let uu____2200 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2201 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2200 uu____2201)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___220_2203  ->
      match uu___220_2203 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) when
          FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t ->
          Prims.strcat "[|" (Prims.strcat s "|]")
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
          let uu____2212 =
            let uu____2213 = term_to_string t  in
            Prims.strcat uu____2213 (Prims.strcat "]" s)  in
          Prims.strcat "#[" uu____2212
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
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun is_arrow  ->
    fun b  ->
      let uu____2227 =
        let uu____2228 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2228  in
      if uu____2227
      then
        let uu____2229 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2229 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2235 = b  in
         match uu____2235 with
         | (a,imp) ->
             let uu____2248 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2248
             then
               let uu____2249 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2249
             else
               (let uu____2251 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2253 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2253)
                   in
                if uu____2251
                then
                  let uu____2254 = nm_to_string a  in
                  imp_to_string uu____2254 imp
                else
                  (let uu____2256 =
                     let uu____2257 = nm_to_string a  in
                     let uu____2258 =
                       let uu____2259 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2259  in
                     Prims.strcat uu____2257 uu____2258  in
                   imp_to_string uu____2256 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.arg_qualifier
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  = fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2273 = FStar_Options.print_implicits ()  in
        if uu____2273 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2277 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2277 (FStar_String.concat sep)
      else
        (let uu____2299 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2299 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___221_2308  ->
    match uu___221_2308 with
    | (a,imp) ->
        let uu____2321 = term_to_string a  in imp_to_string uu____2321 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2332 = FStar_Options.print_implicits ()  in
      if uu____2332 then args else filter_imp args  in
    let uu____2344 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2344 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2367 = FStar_Options.ugly ()  in
      if uu____2367
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2372 =
      let uu____2373 = FStar_Options.ugly ()  in Prims.op_Negation uu____2373
       in
    if uu____2372
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2387 =
             let uu____2388 = FStar_Syntax_Subst.compress t  in
             uu____2388.FStar_Syntax_Syntax.n  in
           (match uu____2387 with
            | FStar_Syntax_Syntax.Tm_type uu____2391 when
                let uu____2392 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2392 -> term_to_string t
            | uu____2393 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2395 = univ_to_string u  in
                     let uu____2396 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2395 uu____2396
                 | uu____2397 ->
                     let uu____2400 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2400))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2411 =
             let uu____2412 = FStar_Syntax_Subst.compress t  in
             uu____2412.FStar_Syntax_Syntax.n  in
           (match uu____2411 with
            | FStar_Syntax_Syntax.Tm_type uu____2415 when
                let uu____2416 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2416 -> term_to_string t
            | uu____2417 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2419 = univ_to_string u  in
                     let uu____2420 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2419 uu____2420
                 | uu____2421 ->
                     let uu____2424 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2424))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2427 = FStar_Options.print_effect_args ()  in
             if uu____2427
             then
               let uu____2428 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2429 =
                 let uu____2430 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2430 (FStar_String.concat ", ")
                  in
               let uu____2439 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2440 =
                 let uu____2441 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2441 (FStar_String.concat ", ")
                  in
               let uu____2462 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2428
                 uu____2429 uu____2439 uu____2440 uu____2462
             else
               (let uu____2464 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___222_2468  ->
                           match uu___222_2468 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2469 -> false)))
                    &&
                    (let uu____2471 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2471)
                   in
                if uu____2464
                then
                  let uu____2472 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2472
                else
                  (let uu____2474 =
                     ((let uu____2477 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2477) &&
                        (let uu____2479 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2479))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2474
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2481 =
                        (let uu____2484 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2484) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___223_2488  ->
                                   match uu___223_2488 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2489 -> false)))
                         in
                      if uu____2481
                      then
                        let uu____2490 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2490
                      else
                        (let uu____2492 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2493 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2492 uu____2493))))
              in
           let dec =
             let uu____2495 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___224_2505  ->
                       match uu___224_2505 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2511 =
                             let uu____2512 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2512
                              in
                           [uu____2511]
                       | uu____2513 -> []))
                in
             FStar_All.pipe_right uu____2495 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2517 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___225_2526  ->
    match uu___225_2526 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2541 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2575 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2597  ->
                              match uu____2597 with
                              | (t,uu____2605) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2575
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2541 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2615 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2615
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2618) ->
        let uu____2619 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2619
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2627 = sli m  in
        let uu____2628 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2627 uu____2628
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2636 = sli m  in
        let uu____2637 = sli m'  in
        let uu____2638 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2636
          uu____2637 uu____2638

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2649 = FStar_Options.ugly ()  in
      if uu____2649
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
      let uu____2663 = b  in
      match uu____2663 with
      | (a,imp) ->
          let n1 =
            let uu____2671 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2671
            then FStar_Util.JsonNull
            else
              (let uu____2673 =
                 let uu____2674 = nm_to_string a  in
                 imp_to_string uu____2674 imp  in
               FStar_Util.JsonStr uu____2673)
             in
          let t =
            let uu____2676 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2676  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2699 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2699
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2713 = FStar_Options.print_universes ()  in
    if uu____2713 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2720 =
      let uu____2721 = FStar_Options.ugly ()  in Prims.op_Negation uu____2721
       in
    if uu____2720
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2725 = s  in
       match uu____2725 with
       | (us,t) ->
           let uu____2736 =
             let uu____2737 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2737  in
           let uu____2738 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2736 uu____2738)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2744 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2745 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2746 =
      let uu____2747 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2747  in
    let uu____2748 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2749 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2744 uu____2745 uu____2746
      uu____2748 uu____2749
  
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
          let uu____2774 =
            let uu____2775 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2775  in
          if uu____2774
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2789 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2789 (FStar_String.concat ",\n\t")
                in
             let uu____2798 =
               let uu____2801 =
                 let uu____2804 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2805 =
                   let uu____2808 =
                     let uu____2809 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2809  in
                   let uu____2810 =
                     let uu____2813 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2814 =
                       let uu____2817 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2818 =
                         let uu____2821 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2822 =
                           let uu____2825 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2826 =
                             let uu____2829 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2830 =
                               let uu____2833 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2834 =
                                 let uu____2837 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2838 =
                                   let uu____2841 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2842 =
                                     let uu____2845 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2846 =
                                       let uu____2849 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2850 =
                                         let uu____2853 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2854 =
                                           let uu____2857 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2858 =
                                             let uu____2861 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2862 =
                                               let uu____2865 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2866 =
                                                 let uu____2869 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2870 =
                                                   let uu____2873 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2873]  in
                                                 uu____2869 :: uu____2870  in
                                               uu____2865 :: uu____2866  in
                                             uu____2861 :: uu____2862  in
                                           uu____2857 :: uu____2858  in
                                         uu____2853 :: uu____2854  in
                                       uu____2849 :: uu____2850  in
                                     uu____2845 :: uu____2846  in
                                   uu____2841 :: uu____2842  in
                                 uu____2837 :: uu____2838  in
                               uu____2833 :: uu____2834  in
                             uu____2829 :: uu____2830  in
                           uu____2825 :: uu____2826  in
                         uu____2821 :: uu____2822  in
                       uu____2817 :: uu____2818  in
                     uu____2813 :: uu____2814  in
                   uu____2808 :: uu____2810  in
                 uu____2804 :: uu____2805  in
               (if for_free then "_for_free " else "") :: uu____2801  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2798)
  
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
          (lid,univs1,tps,k,uu____2898,uu____2899) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____2911 = FStar_Options.print_universes ()  in
          if uu____2911
          then
            let uu____2912 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____2912 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____2917,uu____2918,uu____2919) ->
          let uu____2924 = FStar_Options.print_universes ()  in
          if uu____2924
          then
            let uu____2925 = univ_names_to_string univs1  in
            let uu____2926 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____2925
              lid.FStar_Ident.str uu____2926
          else
            (let uu____2928 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____2928)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____2932 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____2933 =
            let uu____2934 = FStar_Options.print_universes ()  in
            if uu____2934
            then
              let uu____2935 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____2935
            else ""  in
          let uu____2937 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____2932
            lid.FStar_Ident.str uu____2933 uu____2937
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____2941 = FStar_Options.print_universes ()  in
          if uu____2941
          then
            let uu____2942 = univ_names_to_string us  in
            let uu____2943 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____2942 uu____2943
          else
            (let uu____2945 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2945)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____2947) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____2953 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____2953
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2955) ->
          let uu____2964 =
            let uu____2965 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____2965 (FStar_String.concat "\n")  in
          Prims.strcat "(* Sig_bundle *)" uu____2964
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____3001) -> lift_wp
            | (uu____3008,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____3016 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____3016 with
           | (us,t) ->
               let uu____3027 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____3028 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____3029 = univ_names_to_string us  in
               let uu____3030 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____3027
                 uu____3028 uu____3029 uu____3030)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
          let uu____3040 = FStar_Options.print_universes ()  in
          if uu____3040
          then
            let uu____3041 =
              let uu____3046 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____3046  in
            (match uu____3041 with
             | (univs2,t) ->
                 let uu____3059 =
                   let uu____3064 =
                     let uu____3065 = FStar_Syntax_Subst.compress t  in
                     uu____3065.FStar_Syntax_Syntax.n  in
                   match uu____3064 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____3094 -> failwith "impossible"  in
                 (match uu____3059 with
                  | (tps1,c1) ->
                      let uu____3101 = sli l  in
                      let uu____3102 = univ_names_to_string univs2  in
                      let uu____3103 = binders_to_string " " tps1  in
                      let uu____3104 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____3101
                        uu____3102 uu____3103 uu____3104))
          else
            (let uu____3106 = sli l  in
             let uu____3107 = binders_to_string " " tps  in
             let uu____3108 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____3106 uu____3107
               uu____3108)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____3115 =
            let uu____3116 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____3116  in
          let uu____3121 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____3115 uu____3121
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____3122 ->
        let uu____3125 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.strcat uu____3125 (Prims.strcat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____3136 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____3136 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____3142,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____3144;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____3146;
                       FStar_Syntax_Syntax.lbdef = uu____3147;
                       FStar_Syntax_Syntax.lbattrs = uu____3148;
                       FStar_Syntax_Syntax.lbpos = uu____3149;_}::[]),uu____3150)
        ->
        let uu____3171 = lbname_to_string lb  in
        let uu____3172 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____3171 uu____3172
    | uu____3173 ->
        let uu____3174 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____3174 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____3190 = sli m.FStar_Syntax_Syntax.name  in
    let uu____3191 =
      let uu____3192 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____3192 (FStar_String.concat "\n")  in
    let uu____3197 =
      let uu____3198 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____3198 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____3190
      uu____3191 uu____3197
  
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
          (let uu____3232 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3232))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3239 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3239)));
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
           (let uu____3273 = f x  in
            FStar_Util.string_builder_append strb uu____3273);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3280 = f x1  in
                 FStar_Util.string_builder_append strb uu____3280)) xs;
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
           (let uu____3318 = f x  in
            FStar_Util.string_builder_append strb uu____3318);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3325 = f x1  in
                 FStar_Util.string_builder_append strb uu____3325)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3341 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3341
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___226_3352  ->
    match uu___226_3352 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____3362 =
          let uu____3363 =
            let uu____3364 =
              let uu____3365 =
                let uu____3366 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____3366 (FStar_String.concat " ")  in
              Prims.strcat uu____3365 ")"  in
            Prims.strcat " " uu____3364  in
          Prims.strcat h uu____3363  in
        Prims.strcat "(" uu____3362
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____3373 =
          let uu____3374 = emb_typ_to_string a  in
          let uu____3375 =
            let uu____3376 = emb_typ_to_string b  in
            Prims.strcat ") -> " uu____3376  in
          Prims.strcat uu____3374 uu____3375  in
        Prims.strcat "(" uu____3373
  