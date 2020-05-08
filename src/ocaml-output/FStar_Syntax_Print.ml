open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___0_5  ->
    match uu___0_5 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____9 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____9
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____14 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____14
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____18 =
          let uu____20 = delta_depth_to_string d  in
          Prims.op_Hat uu____20 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____18
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____32 = FStar_Options.print_real_names ()  in
    if uu____32
    then FStar_Ident.string_of_lid l
    else
      (let uu____38 = FStar_Ident.ident_of_lid l  in
       FStar_Ident.string_of_id uu____38)
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____60 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname  in
    let uu____62 =
      let uu____64 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____64  in
    Prims.op_Hat uu____60 uu____62
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____74 = FStar_Options.print_real_names ()  in
    if uu____74
    then bv_to_string bv
    else FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____87 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname  in
    let uu____89 =
      let uu____91 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____91  in
    Prims.op_Hat uu____87 uu____89
  
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
      | uu____313 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____326 -> failwith "get_lid"
  
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
  'uuuuuu429 'uuuuuu430 .
    ('uuuuuu429,'uuuuuu430) FStar_Util.either -> Prims.bool
  =
  fun uu___1_440  ->
    match uu___1_440 with
    | FStar_Util.Inl uu____445 -> false
    | FStar_Util.Inr uu____447 -> true
  
let filter_imp :
  'uuuuuu454 .
    ('uuuuuu454 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('uuuuuu454 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___2_509  ->
            match uu___2_509 with
            | (uu____517,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____524,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____525)) -> false
            | (uu____530,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____531)) -> false
            | uu____537 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____555 =
      let uu____556 = FStar_Syntax_Subst.compress e  in
      uu____556.FStar_Syntax_Syntax.n  in
    match uu____555 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____617 =
          (is_lex_cons f) && ((FStar_List.length exps) = (Prims.of_int (2)))
           in
        if uu____617
        then
          let uu____626 =
            let uu____631 = FStar_List.nth exps Prims.int_one  in
            reconstruct_lex uu____631  in
          (match uu____626 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____642 =
                 let uu____645 = FStar_List.nth exps Prims.int_zero  in
                 uu____645 :: xs  in
               FStar_Pervasives_Native.Some uu____642
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____657 ->
        let uu____658 = is_lex_top e  in
        if uu____658
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd::tl ->
          let uu____706 = f hd  in if uu____706 then hd else find f tl
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____738 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____738
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____769 = get_lid e  in find_lid uu____769 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____781 = get_lid e  in find_lid uu____781 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____793 = get_lid t  in find_lid uu____793 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___3_807  ->
    match uu___3_807 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____818 = FStar_Options.hide_uvar_nums ()  in
    if uu____818
    then "?"
    else
      (let uu____825 =
         let uu____827 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____827 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____825)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v  ->
    let uu____839 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.major  in
    let uu____841 = FStar_Util.string_of_int v.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____839 uu____841
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version * FStar_Range.range)
    -> Prims.string)
  =
  fun u  ->
    let uu____871 = FStar_Options.hide_uvar_nums ()  in
    if uu____871
    then "?"
    else
      (let uu____878 =
         let uu____880 =
           let uu____882 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____882 FStar_Util.string_of_int  in
         let uu____886 =
           let uu____888 =
             FStar_All.pipe_right u
               (fun uu____905  ->
                  match uu____905 with
                  | (uu____917,u1,uu____919) -> version_to_string u1)
              in
           Prims.op_Hat ":" uu____888  in
         Prims.op_Hat uu____880 uu____886  in
       Prims.op_Hat "?" uu____878)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n  ->
    fun u  ->
      let uu____950 = FStar_Syntax_Subst.compress_univ u  in
      match uu____950 with
      | FStar_Syntax_Syntax.U_zero  -> (n, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 -> int_of_univ (n + Prims.int_one) u1
      | uu____963 -> (n, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____974 = FStar_Syntax_Subst.compress_univ u  in
    match uu____974 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____987 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____987
    | FStar_Syntax_Syntax.U_name x ->
        let uu____991 = FStar_Ident.string_of_id x  in
        Prims.op_Hat "U_name " uu____991
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____996 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____996
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1001 = int_of_univ Prims.int_one u1  in
        (match uu____1001 with
         | (n,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n
         | (n,FStar_Pervasives_Native.Some u2) ->
             let uu____1022 = univ_to_string u2  in
             let uu____1024 = FStar_Util.string_of_int n  in
             FStar_Util.format2 "(%s + %s)" uu____1022 uu____1024)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____1030 =
          let uu____1032 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____1032 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____1030
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____1051 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____1051 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____1068 = FStar_List.map (fun x  -> FStar_Ident.string_of_id x) us
       in
    FStar_All.pipe_right uu____1068 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___4_1086  ->
    match uu___4_1086 with
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
        let uu____1102 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____1102
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____1107 = lid_to_string l  in
        let uu____1109 = FStar_Ident.string_of_id x  in
        FStar_Util.format2 "(Projector %s %s)" uu____1107 uu____1109
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1122 =
          let uu____1124 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1124  in
        let uu____1125 =
          let uu____1127 =
            FStar_All.pipe_right fns
              (FStar_List.map FStar_Ident.string_of_id)
             in
          FStar_All.pipe_right uu____1127 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____1122 uu____1125
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1153 =
          let uu____1155 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1155  in
        let uu____1156 =
          let uu____1158 =
            FStar_All.pipe_right fns
              (FStar_List.map FStar_Ident.string_of_id)
             in
          FStar_All.pipe_right uu____1158 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1153 uu____1156
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1175 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____1175
    | FStar_Syntax_Syntax.ExceptionConstructor  -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect  -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect  -> "Effect"
    | FStar_Syntax_Syntax.Reifiable  -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        let uu____1183 = FStar_Ident.string_of_lid l  in
        FStar_Util.format1 "(reflect %s)" uu____1183
    | FStar_Syntax_Syntax.OnlyName  -> "OnlyName"
  
let (quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1200 ->
        let uu____1203 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____1203 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1231 ->
        let uu____1234 = quals_to_string quals  in
        Prims.op_Hat uu____1234 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____1421 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____1421
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1425 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____1425
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1429 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____1429
    | FStar_Syntax_Syntax.Tm_uinst uu____1432 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1440 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1442 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1444,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1445;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1459,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1460;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1474 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1494 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1510 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1518 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1536 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1560 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1588 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1603 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed uu____1617 -> "Tm_delayed"
    | FStar_Syntax_Syntax.Tm_meta (uu____1633,m) ->
        let uu____1639 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____1639
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1643 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1646 =
      let uu____1648 = FStar_Options.ugly ()  in Prims.op_Negation uu____1648
       in
    if uu____1646
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1662 = FStar_Options.print_implicits ()  in
         if uu____1662 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1670 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1687,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1713,thunk);
             FStar_Syntax_Syntax.ltyp = uu____1715;
             FStar_Syntax_Syntax.rng = uu____1716;_}
           ->
           let uu____1727 =
             let uu____1729 =
               let uu____1731 = FStar_Thunk.force thunk  in
               term_to_string uu____1731  in
             Prims.op_Hat uu____1729 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____1727
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1737 =
             let uu____1739 =
               let uu____1741 =
                 let uu____1742 =
                   let uu____1751 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1751  in
                 uu____1742 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1741  in
             Prims.op_Hat uu____1739 "]"  in
           Prims.op_Hat "[lazy:" uu____1737
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1820 =
                  match uu____1820 with
                  | (bv,t) ->
                      let uu____1828 = bv_to_string bv  in
                      let uu____1830 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1828 uu____1830
                   in
                let uu____1833 = term_to_string tm  in
                let uu____1835 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1833 uu____1835
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1844 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1844)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_pattern (uu____1848,ps)) ->
           let pats =
             let uu____1888 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1925 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1950  ->
                                 match uu____1950 with
                                 | (t1,uu____1959) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1925
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1888 (FStar_String.concat "\\/")  in
           let uu____1974 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1974
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1988 = tag_of_term t  in
           let uu____1990 = sli m  in
           let uu____1992 = term_to_string t'  in
           let uu____1994 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1988 uu____1990
             uu____1992 uu____1994
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____2009 = tag_of_term t  in
           let uu____2011 = term_to_string t'  in
           let uu____2013 = sli m0  in
           let uu____2015 = sli m1  in
           let uu____2017 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2009
             uu____2011 uu____2013 uu____2015 uu____2017
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____2032 = FStar_Range.string_of_range r  in
           let uu____2034 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2032
             uu____2034
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2043 = lid_to_string l  in
           let uu____2045 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____2047 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2043 uu____2045
             uu____2047
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____2051) ->
           let uu____2056 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2056
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2060 = db_to_string x3  in
           let uu____2062 =
             let uu____2064 =
               let uu____2066 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____2066 ")"  in
             Prims.op_Hat ":(" uu____2064  in
           Prims.op_Hat uu____2060 uu____2062
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2073)) ->
           let uu____2088 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2088
           then ctx_uvar_to_string_aux true u
           else
             (let uu____2095 =
                let uu____2097 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2097  in
              Prims.op_Hat "?" uu____2095)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2120 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2120
           then
             let uu____2124 = ctx_uvar_to_string_aux true u  in
             let uu____2127 =
               let uu____2129 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2129 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2124 uu____2127
           else
             (let uu____2148 =
                let uu____2150 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2150  in
              Prims.op_Hat "?" uu____2148)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2157 = FStar_Options.print_universes ()  in
           if uu____2157
           then
             let uu____2161 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2161
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2189 = binders_to_string " -> " bs  in
           let uu____2192 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2189 uu____2192
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2224 = binders_to_string " " bs  in
                let uu____2227 = term_to_string t2  in
                let uu____2229 =
                  FStar_Ident.string_of_lid
                    rc.FStar_Syntax_Syntax.residual_effect
                   in
                let uu____2231 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2240 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2240)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2224 uu____2227 uu____2229 uu____2231
            | uu____2244 ->
                let uu____2247 = binders_to_string " " bs  in
                let uu____2250 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2247 uu____2250)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2259 = bv_to_string xt  in
           let uu____2261 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2264 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2259 uu____2261 uu____2264
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2296 = term_to_string t  in
           let uu____2298 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2296 uu____2298
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2321 = lbs_to_string [] lbs  in
           let uu____2323 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2321 uu____2323
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2388 =
                   let uu____2390 =
                     FStar_Util.map_opt eff_name FStar_Ident.string_of_lid
                      in
                   FStar_All.pipe_right uu____2390
                     (FStar_Util.dflt "default")
                    in
                 let uu____2401 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2388 uu____2401
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2422 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2422
              in
           let uu____2425 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2425 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head,branches) ->
           let uu____2466 = term_to_string head  in
           let uu____2468 =
             let uu____2470 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string)
                in
             FStar_Util.concat_l "\n\t|" uu____2470  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2466 uu____2468
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2488 = FStar_Options.print_universes ()  in
           if uu____2488
           then
             let uu____2492 = term_to_string t  in
             let uu____2494 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2492 uu____2494
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____2500  ->
    match uu____2500 with
    | (p,wopt,e) ->
        let uu____2522 = FStar_All.pipe_right p pat_to_string  in
        let uu____2525 =
          match wopt with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____2536 = FStar_All.pipe_right w term_to_string  in
              FStar_Util.format1 "when %s" uu____2536
           in
        let uu____2540 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format3 "%s %s -> %s" uu____2522 uu____2525 uu____2540

and (ctx_uvar_to_string_aux :
  Prims.bool -> FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun print_reason  ->
    fun ctx_uvar  ->
      let reason_string =
        if print_reason
        then
          FStar_Util.format1 "(* %s *)\n"
            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason
        else ""  in
      let uu____2555 =
        binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
         in
      let uu____2558 =
        uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
      let uu____2560 =
        term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
      FStar_Util.format4 "%s(%s |- %s : %s)" reason_string uu____2555
        uu____2558 uu____2560

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2563  ->
    match uu___5_2563 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2569 = FStar_Util.string_of_int i  in
        let uu____2571 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2569 uu____2571
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2578 = bv_to_string x  in
        let uu____2580 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2578 uu____2580
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2589 = bv_to_string x  in
        let uu____2591 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2589 uu____2591
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2598 = FStar_Util.string_of_int i  in
        let uu____2600 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2598 uu____2600
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2607 = FStar_Ident.string_of_id u  in
        let uu____2609 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" uu____2607 uu____2609

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2613 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2613 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2629 =
      let uu____2631 = FStar_Options.ugly ()  in Prims.op_Negation uu____2631
       in
    if uu____2629
    then
      let e =
        let uu____2636 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2636  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2665 = fv_to_string l  in
           let uu____2667 =
             let uu____2669 =
               FStar_List.map
                 (fun uu____2683  ->
                    match uu____2683 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2669 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2665 uu____2667
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2708) ->
           let uu____2713 = FStar_Options.print_bound_var_types ()  in
           if uu____2713
           then
             let uu____2717 = bv_to_string x1  in
             let uu____2719 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2717 uu____2719
           else
             (let uu____2724 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2724)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2728 = FStar_Options.print_bound_var_types ()  in
           if uu____2728
           then
             let uu____2732 = bv_to_string x1  in
             let uu____2734 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2732 uu____2734
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2741 = FStar_Options.print_bound_var_types ()  in
           if uu____2741
           then
             let uu____2745 = bv_to_string x1  in
             let uu____2747 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2745 uu____2747
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2756 = quals_to_string' quals  in
      let uu____2758 =
        let uu____2760 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2780 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2782 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2784 =
                    let uu____2786 = FStar_Options.print_universes ()  in
                    if uu____2786
                    then
                      let uu____2790 =
                        let uu____2792 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____2792 ">"  in
                      Prims.op_Hat "<" uu____2790
                    else ""  in
                  let uu____2799 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2801 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2780
                    uu____2782 uu____2784 uu____2799 uu____2801))
           in
        FStar_Util.concat_l "\n and " uu____2760  in
      FStar_Util.format3 "%slet %s %s" uu____2756
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2758

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2816  ->
    match uu___6_2816 with
    | [] -> ""
    | tms ->
        let uu____2824 =
          let uu____2826 =
            FStar_List.map
              (fun t  ->
                 let uu____2834 = term_to_string t  in paren uu____2834) tms
             in
          FStar_All.pipe_right uu____2826 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2824

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___7_2843  ->
      match uu___7_2843 with
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
          let uu____2861 =
            let uu____2863 = term_to_string t  in
            Prims.op_Hat uu____2863 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____2861
      | FStar_Pervasives_Native.None  -> s

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
      let uu____2881 =
        let uu____2883 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2883  in
      if uu____2881
      then
        let uu____2887 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2887 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
        (let uu____2898 = b  in
         match uu____2898 with
         | (a,imp) ->
             let uu____2912 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2912
             then
               let uu____2916 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat "_:" uu____2916
             else
               (let uu____2921 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2924 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2924)
                   in
                if uu____2921
                then
                  let uu____2928 = nm_to_string a  in
                  imp_to_string uu____2928 imp
                else
                  (let uu____2932 =
                     let uu____2934 = nm_to_string a  in
                     let uu____2936 =
                       let uu____2938 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____2938  in
                     Prims.op_Hat uu____2934 uu____2936  in
                   imp_to_string uu____2932 imp)))

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
        let uu____2957 = FStar_Options.print_implicits ()  in
        if uu____2957 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2968 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2968 (FStar_String.concat sep)
      else
        (let uu____2996 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2996 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_3010  ->
    match uu___8_3010 with
    | (a,imp) ->
        let uu____3024 = term_to_string a  in imp_to_string uu____3024 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____3036 = FStar_Options.print_implicits ()  in
      if uu____3036 then args else filter_imp args  in
    let uu____3051 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____3051 (FStar_String.concat " ")

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____3079 =
      let uu____3081 = FStar_Options.ugly ()  in Prims.op_Negation uu____3081
       in
    if uu____3079
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____3102 =
             let uu____3103 = FStar_Syntax_Subst.compress t  in
             uu____3103.FStar_Syntax_Syntax.n  in
           (match uu____3102 with
            | FStar_Syntax_Syntax.Tm_type uu____3107 when
                let uu____3108 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3108 -> term_to_string t
            | uu____3110 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3113 = univ_to_string u  in
                     let uu____3115 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3113 uu____3115
                 | uu____3118 ->
                     let uu____3121 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3121))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3134 =
             let uu____3135 = FStar_Syntax_Subst.compress t  in
             uu____3135.FStar_Syntax_Syntax.n  in
           (match uu____3134 with
            | FStar_Syntax_Syntax.Tm_type uu____3139 when
                let uu____3140 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3140 -> term_to_string t
            | uu____3142 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3145 = univ_to_string u  in
                     let uu____3147 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3145 uu____3147
                 | uu____3150 ->
                     let uu____3153 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3153))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3159 = FStar_Options.print_effect_args ()  in
             if uu____3159
             then
               let uu____3163 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3165 =
                 let uu____3167 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3167 (FStar_String.concat ", ")
                  in
               let uu____3182 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3184 =
                 let uu____3186 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3186 (FStar_String.concat ", ")
                  in
               let uu____3213 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3163
                 uu____3165 uu____3182 uu____3184 uu____3213
             else
               (let uu____3218 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3224  ->
                           match uu___9_3224 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3227 -> false)))
                    &&
                    (let uu____3230 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3230)
                   in
                if uu____3218
                then
                  let uu____3234 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3234
                else
                  (let uu____3239 =
                     ((let uu____3243 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3243) &&
                        (let uu____3246 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3246))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____3239
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3252 =
                        (let uu____3256 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3256) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3262  ->
                                   match uu___10_3262 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3265 -> false)))
                         in
                      if uu____3252
                      then
                        let uu____3269 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3269
                      else
                        (let uu____3274 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3276 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3274 uu____3276))))
              in
           let dec =
             let uu____3281 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3294  ->
                       match uu___11_3294 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3301 =
                             let uu____3303 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3303
                              in
                           [uu____3301]
                       | uu____3308 -> []))
                in
             FStar_All.pipe_right uu____3281 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____3327 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_3337  ->
    match uu___12_3337 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____3339,ps) ->
        let pats =
          let uu____3375 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3412 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3437  ->
                              match uu____3437 with
                              | (t,uu____3446) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3412
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3375 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3463 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3463
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3468) ->
        let uu____3473 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3473
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____3484 = sli m  in
        let uu____3486 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3484 uu____3486
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3496 = sli m  in
        let uu____3498 = sli m'  in
        let uu____3500 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3496
          uu____3498 uu____3500

let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq  -> aqual_to_string' "" aq 
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____3523 = FStar_Options.ugly ()  in
      if uu____3523
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)
  
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____3545 = FStar_Options.ugly ()  in
      if uu____3545
      then term_to_string x
      else
        (let e = FStar_Syntax_Resugar.resugar_term' env x  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.of_int (100)) d)
  
let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env  ->
    fun b  ->
      let uu____3566 = b  in
      match uu____3566 with
      | (a,imp) ->
          let n =
            let uu____3574 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3574
            then FStar_Util.JsonNull
            else
              (let uu____3579 =
                 let uu____3581 = nm_to_string a  in
                 imp_to_string uu____3581 imp  in
               FStar_Util.JsonStr uu____3579)
             in
          let t =
            let uu____3584 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3584  in
          FStar_Util.JsonAssoc [("name", n); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____3616 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3616
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3634 = FStar_Options.print_universes ()  in
    if uu____3634 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3650 =
      let uu____3652 = FStar_Options.ugly ()  in Prims.op_Negation uu____3652
       in
    if uu____3650
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
      (let uu____3662 = s  in
       match uu____3662 with
       | (us,t) ->
           let uu____3674 =
             let uu____3676 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3676  in
           let uu____3680 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3674 uu____3680)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3690 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3692 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3695 =
      let uu____3697 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3697  in
    let uu____3701 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3703 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3690 uu____3692 uu____3695
      uu____3701 uu____3703
  
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs  ->
    let tscheme_opt_to_string uu___13_3721 =
      match uu___13_3721 with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None  -> "None"  in
    let uu____3727 =
      let uu____3731 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____3733 =
        let uu____3737 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp
           in
        let uu____3739 =
          let uu____3743 =
            tscheme_to_string combs.FStar_Syntax_Syntax.stronger  in
          let uu____3745 =
            let uu____3749 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else  in
            let uu____3751 =
              let uu____3755 =
                tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp  in
              let uu____3757 =
                let uu____3761 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp  in
                let uu____3763 =
                  let uu____3767 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial  in
                  let uu____3769 =
                    let uu____3773 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr
                       in
                    let uu____3775 =
                      let uu____3779 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr
                         in
                      let uu____3781 =
                        let uu____3785 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr
                           in
                        [uu____3785]  in
                      uu____3779 :: uu____3781  in
                    uu____3773 :: uu____3775  in
                  uu____3767 :: uu____3769  in
                uu____3761 :: uu____3763  in
              uu____3755 :: uu____3757  in
            uu____3749 :: uu____3751  in
          uu____3743 :: uu____3745  in
        uu____3737 :: uu____3739  in
      uu____3731 :: uu____3733  in
    FStar_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu____3727
  
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs  ->
    let to_str uu____3816 =
      match uu____3816 with
      | (ts_t,ts_ty) ->
          let uu____3824 = tscheme_to_string ts_t  in
          let uu____3826 = tscheme_to_string ts_ty  in
          FStar_Util.format2 "(%s) : (%s)" uu____3824 uu____3826
       in
    let uu____3829 =
      let uu____3833 =
        FStar_Ident.string_of_lid combs.FStar_Syntax_Syntax.l_base_effect  in
      let uu____3835 =
        let uu____3839 = to_str combs.FStar_Syntax_Syntax.l_repr  in
        let uu____3841 =
          let uu____3845 = to_str combs.FStar_Syntax_Syntax.l_return  in
          let uu____3847 =
            let uu____3851 = to_str combs.FStar_Syntax_Syntax.l_bind  in
            let uu____3853 =
              let uu____3857 = to_str combs.FStar_Syntax_Syntax.l_subcomp  in
              let uu____3859 =
                let uu____3863 =
                  to_str combs.FStar_Syntax_Syntax.l_if_then_else  in
                [uu____3863]  in
              uu____3857 :: uu____3859  in
            uu____3851 :: uu____3853  in
          uu____3845 :: uu____3847  in
        uu____3839 :: uu____3841  in
      uu____3833 :: uu____3835  in
    FStar_Util.format
      "{\nl_base_effect = %s\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  }\n"
      uu____3829
  
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___14_3879  ->
    match uu___14_3879 with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        wp_eff_combinators_to_string combs
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        wp_eff_combinators_to_string combs
    | FStar_Syntax_Syntax.Layered_eff combs ->
        layered_eff_combinators_to_string combs
  
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
          let uu____3912 =
            let uu____3914 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3914  in
          if uu____3912
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
               let uu____3935 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3935 (FStar_String.concat ",\n\t")
                in
             let eff_name =
               let uu____3952 = FStar_Syntax_Util.is_layered ed  in
               if uu____3952 then "layered_effect" else "new_effect"  in
             let uu____3960 =
               let uu____3964 =
                 let uu____3968 =
                   let uu____3972 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname  in
                   let uu____3974 =
                     let uu____3978 =
                       let uu____3980 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs
                          in
                       FStar_All.pipe_left enclose_universes uu____3980  in
                     let uu____3984 =
                       let uu____3988 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders
                          in
                       let uu____3991 =
                         let uu____3995 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature
                            in
                         let uu____3997 =
                           let uu____4001 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____4003 =
                             let uu____4007 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions
                                in
                             [uu____4007]  in
                           uu____4001 :: uu____4003  in
                         uu____3995 :: uu____3997  in
                       uu____3988 :: uu____3991  in
                     uu____3978 :: uu____3984  in
                   uu____3972 :: uu____3974  in
                 (if for_free then "_for_free " else "") :: uu____3968  in
               eff_name :: uu____3964  in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu____3960)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se  ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
        let uu____4059 = FStar_All.pipe_right ts_opt FStar_Util.must  in
        FStar_All.pipe_right uu____4059 tscheme_to_string
      else "<None>"  in
    let uu____4066 = lid_to_string se.FStar_Syntax_Syntax.source  in
    let uu____4068 = lid_to_string se.FStar_Syntax_Syntax.target  in
    let uu____4070 = tsopt_to_string se.FStar_Syntax_Syntax.lift  in
    let uu____4072 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp  in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____4066 uu____4068 uu____4070 uu____4072
  
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
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.RestartSolver )
          -> "#restart-solver"
      | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.PopOptions ) ->
          "#pop-options"
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univs,tps,k,uu____4107,uu____4108) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4124 = FStar_Options.print_universes ()  in
          if uu____4124
          then
            let uu____4128 = FStar_Ident.string_of_lid lid  in
            let uu____4130 = univ_names_to_string univs  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str uu____4128
              uu____4130 binders_str term_str
          else
            (let uu____4135 = FStar_Ident.string_of_lid lid  in
             FStar_Util.format4 "%stype %s %s : %s" quals_str uu____4135
               binders_str term_str)
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs,t,uu____4141,uu____4142,uu____4143) ->
          let uu____4150 = FStar_Options.print_universes ()  in
          if uu____4150
          then
            let uu____4154 = univ_names_to_string univs  in
            let uu____4156 = FStar_Ident.string_of_lid lid  in
            let uu____4158 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4154 uu____4156
              uu____4158
          else
            (let uu____4163 = FStar_Ident.string_of_lid lid  in
             let uu____4165 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" uu____4163 uu____4165)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs,t) ->
          let uu____4171 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4173 = FStar_Ident.string_of_lid lid  in
          let uu____4175 =
            let uu____4177 = FStar_Options.print_universes ()  in
            if uu____4177
            then
              let uu____4181 = univ_names_to_string univs  in
              FStar_Util.format1 "<%s>" uu____4181
            else ""  in
          let uu____4187 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4171 uu____4173
            uu____4175 uu____4187
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4193 = FStar_Options.print_universes ()  in
          if uu____4193
          then
            let uu____4197 = FStar_Ident.string_of_lid lid  in
            let uu____4199 = univ_names_to_string us  in
            let uu____4201 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" uu____4197 uu____4199
              uu____4201
          else
            (let uu____4206 = FStar_Ident.string_of_lid lid  in
             let uu____4208 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" uu____4206 uu____4208)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4212) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4218) ->
          let uu____4227 =
            let uu____4229 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4229 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____4227
      | FStar_Syntax_Syntax.Sig_fail (errs,lax,ses) ->
          let uu____4255 = FStar_Util.string_of_bool lax  in
          let uu____4257 =
            FStar_Common.string_of_list FStar_Util.string_of_int errs  in
          let uu____4260 =
            let uu____4262 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4262 (FStar_String.concat "\n")  in
          FStar_Util.format3 "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n"
            uu____4255 uu____4257 uu____4260
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4274 = FStar_Syntax_Util.is_dm4f ed  in
          eff_decl_to_string' uu____4274 x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs,tps,c,flags) ->
          let uu____4286 = FStar_Options.print_universes ()  in
          if uu____4286
          then
            let uu____4290 =
              let uu____4295 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs uu____4295  in
            (match uu____4290 with
             | (univs1,t) ->
                 let uu____4309 =
                   let uu____4314 =
                     let uu____4315 = FStar_Syntax_Subst.compress t  in
                     uu____4315.FStar_Syntax_Syntax.n  in
                   match uu____4314 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4344 -> failwith "impossible"  in
                 (match uu____4309 with
                  | (tps1,c1) ->
                      let uu____4353 = sli l  in
                      let uu____4355 = univ_names_to_string univs1  in
                      let uu____4357 = binders_to_string " " tps1  in
                      let uu____4360 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4353
                        uu____4355 uu____4357 uu____4360))
          else
            (let uu____4365 = sli l  in
             let uu____4367 = binders_to_string " " tps  in
             let uu____4370 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4365 uu____4367
               uu____4370)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4379 =
            let uu____4381 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4381  in
          let uu____4391 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4379 uu____4391
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,t,ty) ->
          let uu____4399 = FStar_Ident.string_of_lid m  in
          let uu____4401 = FStar_Ident.string_of_lid n  in
          let uu____4403 = FStar_Ident.string_of_lid p  in
          let uu____4405 = tscheme_to_string t  in
          let uu____4407 = tscheme_to_string ty  in
          FStar_Util.format5 "polymonadic_bind (%s, %s) |> %s = (%s, %s)"
            uu____4399 uu____4401 uu____4403 uu____4405 uu____4407
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp (m,n,t,ty) ->
          let uu____4414 = FStar_Ident.string_of_lid m  in
          let uu____4416 = FStar_Ident.string_of_lid n  in
          let uu____4418 = tscheme_to_string t  in
          let uu____4420 = tscheme_to_string ty  in
          FStar_Util.format4 "polymonadic_subcomp %s <: %s = (%s, %s)"
            uu____4414 uu____4416 uu____4418 uu____4420
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4426 ->
        let uu____4429 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____4429 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____4446 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4446 msg
  
let (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4457,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4459;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4461;
                       FStar_Syntax_Syntax.lbdef = uu____4462;
                       FStar_Syntax_Syntax.lbattrs = uu____4463;
                       FStar_Syntax_Syntax.lbpos = uu____4464;_}::[]),uu____4465)
        ->
        let uu____4488 = lbname_to_string lb  in
        let uu____4490 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4488 uu____4490
    | uu____4493 ->
        let uu____4494 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> FStar_Ident.string_of_lid l))
           in
        FStar_All.pipe_right uu____4494 (FStar_String.concat ", ")
  
let (tag_of_sigelt : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4520 -> "Sig_inductive_typ"
    | FStar_Syntax_Syntax.Sig_bundle uu____4538 -> "Sig_bundle"
    | FStar_Syntax_Syntax.Sig_datacon uu____4548 -> "Sig_datacon"
    | FStar_Syntax_Syntax.Sig_declare_typ uu____4565 -> "Sig_declare_typ"
    | FStar_Syntax_Syntax.Sig_let uu____4573 -> "Sig_let"
    | FStar_Syntax_Syntax.Sig_assume uu____4581 -> "Sig_assume"
    | FStar_Syntax_Syntax.Sig_new_effect uu____4589 -> "Sig_new_effect"
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4591 -> "Sig_sub_effect"
    | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4593 -> "Sig_effect_abbrev"
    | FStar_Syntax_Syntax.Sig_pragma uu____4607 -> "Sig_pragma"
    | FStar_Syntax_Syntax.Sig_splice uu____4609 -> "Sig_splice"
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____4617 ->
        "Sig_polymonadic_bind"
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____4629 ->
        "Sig_polymonadic_subcomp"
    | FStar_Syntax_Syntax.Sig_fail uu____4639 -> "Sig_fail"
  
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4660 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4662 =
      let uu____4664 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4664 (FStar_String.concat "\n")  in
    let uu____4674 =
      let uu____4676 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4676 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4660
      uu____4662 uu____4674
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
           (let uu____4726 = f x  in
            FStar_Util.string_builder_append strb uu____4726);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4735 = f x1  in
                 FStar_Util.string_builder_append strb uu____4735)) xs;
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
           (let uu____4782 = f x  in
            FStar_Util.string_builder_append strb uu____4782);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4791 = f x1  in
                 FStar_Util.string_builder_append strb uu____4791)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____4813 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4813
  
let (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> ctx_uvar_to_string_aux true ctx_uvar 
let (ctx_uvar_to_string_no_reason :
  FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> ctx_uvar_to_string_aux false ctx_uvar 
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___15_4842  ->
    match uu___15_4842 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4858 =
          let uu____4860 =
            let uu____4862 =
              let uu____4864 =
                let uu____4866 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4866 (FStar_String.concat " ")  in
              Prims.op_Hat uu____4864 ")"  in
            Prims.op_Hat " " uu____4862  in
          Prims.op_Hat h uu____4860  in
        Prims.op_Hat "(" uu____4858
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4881 =
          let uu____4883 = emb_typ_to_string a  in
          let uu____4885 =
            let uu____4887 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____4887  in
          Prims.op_Hat uu____4883 uu____4885  in
        Prims.op_Hat "(" uu____4881
  