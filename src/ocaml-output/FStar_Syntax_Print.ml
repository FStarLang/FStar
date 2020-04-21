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
       FStar_Ident.text_of_id uu____38)
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____60 = FStar_Ident.text_of_id bv.FStar_Syntax_Syntax.ppname  in
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
    else FStar_Ident.text_of_id bv.FStar_Syntax_Syntax.ppname
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____87 = FStar_Ident.text_of_id bv.FStar_Syntax_Syntax.ppname  in
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
        let uu____991 = FStar_Ident.text_of_id x  in
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
    let uu____1068 = FStar_List.map (fun x  -> FStar_Ident.text_of_id x) us
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
        let uu____1109 = FStar_Ident.text_of_id x  in
        FStar_Util.format2 "(Projector %s %s)" uu____1107 uu____1109
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1122 =
          let uu____1124 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1124  in
        let uu____1125 =
          let uu____1127 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1127 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____1122 uu____1125
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1153 =
          let uu____1155 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1155  in
        let uu____1156 =
          let uu____1158 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
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
        let uu____1416 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____1416
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____1420 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____1420
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____1424 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____1424
    | FStar_Syntax_Syntax.Tm_uinst uu____1427 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____1435 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____1437 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1439,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_static ;
                      FStar_Syntax_Syntax.antiquotes = uu____1440;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1454,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1455;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1469 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1489 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1505 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1513 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1531 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1555 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1583 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1598 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed uu____1612 -> "Tm_delayed"
    | FStar_Syntax_Syntax.Tm_meta (uu____1628,m) ->
        let uu____1634 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____1634
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1638 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1641 =
      let uu____1643 = FStar_Options.ugly ()  in Prims.op_Negation uu____1643
       in
    if uu____1641
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1657 = FStar_Options.print_implicits ()  in
         if uu____1657 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1665 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1682,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____1708,thunk);
             FStar_Syntax_Syntax.ltyp = uu____1710;
             FStar_Syntax_Syntax.rng = uu____1711;_}
           ->
           let uu____1722 =
             let uu____1724 =
               let uu____1726 = FStar_Thunk.force thunk  in
               term_to_string uu____1726  in
             Prims.op_Hat uu____1724 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____1722
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1732 =
             let uu____1734 =
               let uu____1736 =
                 let uu____1737 =
                   let uu____1746 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____1746  in
                 uu____1737 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____1736  in
             Prims.op_Hat uu____1734 "]"  in
           Prims.op_Hat "[lazy:" uu____1732
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____1815 =
                  match uu____1815 with
                  | (bv,t) ->
                      let uu____1823 = bv_to_string bv  in
                      let uu____1825 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____1823 uu____1825
                   in
                let uu____1828 = term_to_string tm  in
                let uu____1830 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____1828 uu____1830
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____1839 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____1839)
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_pattern (uu____1843,ps)) ->
           let pats =
             let uu____1883 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1920 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1945  ->
                                 match uu____1945 with
                                 | (t1,uu____1954) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1920
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1883 (FStar_String.concat "\\/")  in
           let uu____1969 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1969
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1983 = tag_of_term t  in
           let uu____1985 = sli m  in
           let uu____1987 = term_to_string t'  in
           let uu____1989 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1983 uu____1985
             uu____1987 uu____1989
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____2004 = tag_of_term t  in
           let uu____2006 = term_to_string t'  in
           let uu____2008 = sli m0  in
           let uu____2010 = sli m1  in
           let uu____2012 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____2004
             uu____2006 uu____2008 uu____2010 uu____2012
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____2027 = FStar_Range.string_of_range r  in
           let uu____2029 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____2027
             uu____2029
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____2038 = lid_to_string l  in
           let uu____2040 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____2042 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____2038 uu____2040
             uu____2042
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____2046) ->
           let uu____2051 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____2051
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____2055 = db_to_string x3  in
           let uu____2057 =
             let uu____2059 =
               let uu____2061 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____2061 ")"  in
             Prims.op_Hat ":(" uu____2059  in
           Prims.op_Hat uu____2055 uu____2057
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____2068)) ->
           let uu____2083 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2083
           then ctx_uvar_to_string u
           else
             (let uu____2089 =
                let uu____2091 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2091  in
              Prims.op_Hat "?" uu____2089)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____2114 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____2114
           then
             let uu____2118 = ctx_uvar_to_string u  in
             let uu____2120 =
               let uu____2122 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____2122 (FStar_String.concat "; ")  in
             FStar_Util.format2 "(%s @ %s)" uu____2118 uu____2120
           else
             (let uu____2141 =
                let uu____2143 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____2143  in
              Prims.op_Hat "?" uu____2141)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____2150 = FStar_Options.print_universes ()  in
           if uu____2150
           then
             let uu____2154 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____2154
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____2182 = binders_to_string " -> " bs  in
           let uu____2185 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____2182 uu____2185
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____2217 = binders_to_string " " bs  in
                let uu____2220 = term_to_string t2  in
                let uu____2222 =
                  FStar_Ident.string_of_lid
                    rc.FStar_Syntax_Syntax.residual_effect
                   in
                let uu____2224 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____2233 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____2233)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____2217 uu____2220 uu____2222 uu____2224
            | uu____2237 ->
                let uu____2240 = binders_to_string " " bs  in
                let uu____2243 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____2240 uu____2243)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____2252 = bv_to_string xt  in
           let uu____2254 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____2257 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____2252 uu____2254 uu____2257
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____2289 = term_to_string t  in
           let uu____2291 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____2289 uu____2291
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____2314 = lbs_to_string [] lbs  in
           let uu____2316 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____2314 uu____2316
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____2381 =
                   let uu____2383 =
                     FStar_Util.map_opt eff_name FStar_Ident.string_of_lid
                      in
                   FStar_All.pipe_right uu____2383
                     (FStar_Util.dflt "default")
                    in
                 let uu____2394 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____2381 uu____2394
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____2415 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____2415
              in
           let uu____2418 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____2418 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head,branches) ->
           let uu____2459 = term_to_string head  in
           let uu____2461 =
             let uu____2463 =
               FStar_All.pipe_right branches
                 (FStar_List.map branch_to_string)
                in
             FStar_Util.concat_l "\n\t|" uu____2463  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____2459 uu____2461
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____2481 = FStar_Options.print_universes ()  in
           if uu____2481
           then
             let uu____2485 = term_to_string t  in
             let uu____2487 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____2485 uu____2487
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (branch_to_string : FStar_Syntax_Syntax.branch -> Prims.string) =
  fun uu____2493  ->
    match uu____2493 with
    | (p,wopt,e) ->
        let uu____2515 = FStar_All.pipe_right p pat_to_string  in
        let uu____2518 =
          match wopt with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some w ->
              let uu____2529 = FStar_All.pipe_right w term_to_string  in
              FStar_Util.format1 "when %s" uu____2529
           in
        let uu____2533 = FStar_All.pipe_right e term_to_string  in
        FStar_Util.format3 "%s %s -> %s" uu____2515 uu____2518 uu____2533

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____2538 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____2541 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____2543 = term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ
       in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____2538 uu____2541
      uu____2543

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___5_2546  ->
    match uu___5_2546 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2552 = FStar_Util.string_of_int i  in
        let uu____2554 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2552 uu____2554
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2561 = bv_to_string x  in
        let uu____2563 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2561 uu____2563
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2572 = bv_to_string x  in
        let uu____2574 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____2572 uu____2574
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2581 = FStar_Util.string_of_int i  in
        let uu____2583 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2581 uu____2583
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2590 = FStar_Ident.text_of_id u  in
        let uu____2592 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" uu____2590 uu____2592

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2596 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2596 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____2612 =
      let uu____2614 = FStar_Options.ugly ()  in Prims.op_Negation uu____2614
       in
    if uu____2612
    then
      let e =
        let uu____2619 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____2619  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____2648 = fv_to_string l  in
           let uu____2650 =
             let uu____2652 =
               FStar_List.map
                 (fun uu____2666  ->
                    match uu____2666 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____2652 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____2648 uu____2650
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____2691) ->
           let uu____2696 = FStar_Options.print_bound_var_types ()  in
           if uu____2696
           then
             let uu____2700 = bv_to_string x1  in
             let uu____2702 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____2700 uu____2702
           else
             (let uu____2707 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____2707)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____2711 = FStar_Options.print_bound_var_types ()  in
           if uu____2711
           then
             let uu____2715 = bv_to_string x1  in
             let uu____2717 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____2715 uu____2717
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____2724 = FStar_Options.print_bound_var_types ()  in
           if uu____2724
           then
             let uu____2728 = bv_to_string x1  in
             let uu____2730 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____2728 uu____2730
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____2739 = quals_to_string' quals  in
      let uu____2741 =
        let uu____2743 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2763 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2765 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2767 =
                    let uu____2769 = FStar_Options.print_universes ()  in
                    if uu____2769
                    then
                      let uu____2773 =
                        let uu____2775 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____2775 ">"  in
                      Prims.op_Hat "<" uu____2773
                    else ""  in
                  let uu____2782 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2784 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2763
                    uu____2765 uu____2767 uu____2782 uu____2784))
           in
        FStar_Util.concat_l "\n and " uu____2743  in
      FStar_Util.format3 "%slet %s %s" uu____2739
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____2741

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___6_2799  ->
    match uu___6_2799 with
    | [] -> ""
    | tms ->
        let uu____2807 =
          let uu____2809 =
            FStar_List.map
              (fun t  ->
                 let uu____2817 = term_to_string t  in paren uu____2817) tms
             in
          FStar_All.pipe_right uu____2809 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2807

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___7_2826  ->
      match uu___7_2826 with
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
          let uu____2844 =
            let uu____2846 = term_to_string t  in
            Prims.op_Hat uu____2846 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____2844
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
      let uu____2864 =
        let uu____2866 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2866  in
      if uu____2864
      then
        let uu____2870 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2870 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d
      else
        (let uu____2881 = b  in
         match uu____2881 with
         | (a,imp) ->
             let uu____2895 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2895
             then
               let uu____2899 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat "_:" uu____2899
             else
               (let uu____2904 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2907 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2907)
                   in
                if uu____2904
                then
                  let uu____2911 = nm_to_string a  in
                  imp_to_string uu____2911 imp
                else
                  (let uu____2915 =
                     let uu____2917 = nm_to_string a  in
                     let uu____2919 =
                       let uu____2921 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____2921  in
                     Prims.op_Hat uu____2917 uu____2919  in
                   imp_to_string uu____2915 imp)))

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
        let uu____2940 = FStar_Options.print_implicits ()  in
        if uu____2940 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2951 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2951 (FStar_String.concat sep)
      else
        (let uu____2979 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2979 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___8_2993  ->
    match uu___8_2993 with
    | (a,imp) ->
        let uu____3007 = term_to_string a  in imp_to_string uu____3007 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____3019 = FStar_Options.print_implicits ()  in
      if uu____3019 then args else filter_imp args  in
    let uu____3034 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____3034 (FStar_String.concat " ")

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____3062 =
      let uu____3064 = FStar_Options.ugly ()  in Prims.op_Negation uu____3064
       in
    if uu____3062
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____3085 =
             let uu____3086 = FStar_Syntax_Subst.compress t  in
             uu____3086.FStar_Syntax_Syntax.n  in
           (match uu____3085 with
            | FStar_Syntax_Syntax.Tm_type uu____3090 when
                let uu____3091 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3091 -> term_to_string t
            | uu____3093 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3096 = univ_to_string u  in
                     let uu____3098 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____3096 uu____3098
                 | uu____3101 ->
                     let uu____3104 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____3104))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____3117 =
             let uu____3118 = FStar_Syntax_Subst.compress t  in
             uu____3118.FStar_Syntax_Syntax.n  in
           (match uu____3117 with
            | FStar_Syntax_Syntax.Tm_type uu____3122 when
                let uu____3123 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____3123 -> term_to_string t
            | uu____3125 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____3128 = univ_to_string u  in
                     let uu____3130 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____3128 uu____3130
                 | uu____3133 ->
                     let uu____3136 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____3136))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____3142 = FStar_Options.print_effect_args ()  in
             if uu____3142
             then
               let uu____3146 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____3148 =
                 let uu____3150 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____3150 (FStar_String.concat ", ")
                  in
               let uu____3165 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____3167 =
                 let uu____3169 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____3169 (FStar_String.concat ", ")
                  in
               let uu____3196 = cflags_to_string c1.FStar_Syntax_Syntax.flags
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____3146
                 uu____3148 uu____3165 uu____3167 uu____3196
             else
               (let uu____3201 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___9_3207  ->
                           match uu___9_3207 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____3210 -> false)))
                    &&
                    (let uu____3213 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____3213)
                   in
                if uu____3201
                then
                  let uu____3217 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____3217
                else
                  (let uu____3222 =
                     ((let uu____3226 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____3226) &&
                        (let uu____3229 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____3229))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____3222
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____3235 =
                        (let uu____3239 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____3239) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___10_3245  ->
                                   match uu___10_3245 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____3248 -> false)))
                         in
                      if uu____3235
                      then
                        let uu____3252 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____3252
                      else
                        (let uu____3257 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____3259 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____3257 uu____3259))))
              in
           let dec =
             let uu____3264 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___11_3277  ->
                       match uu___11_3277 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____3284 =
                             let uu____3286 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____3286
                              in
                           [uu____3284]
                       | uu____3291 -> []))
                in
             FStar_All.pipe_right uu____3264 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____3310 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___12_3320  ->
    match uu___12_3320 with
    | FStar_Syntax_Syntax.Meta_pattern (uu____3322,ps) ->
        let pats =
          let uu____3358 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____3395 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____3420  ->
                              match uu____3420 with
                              | (t,uu____3429) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____3395
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____3358 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____3446 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____3446
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____3451) ->
        let uu____3456 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____3456
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____3467 = sli m  in
        let uu____3469 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____3467 uu____3469
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____3479 = sli m  in
        let uu____3481 = sli m'  in
        let uu____3483 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____3479
          uu____3481 uu____3483

let (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun aq  -> aqual_to_string' "" aq 
let (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____3506 = FStar_Options.ugly ()  in
      if uu____3506
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
      let uu____3528 = FStar_Options.ugly ()  in
      if uu____3528
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
      let uu____3549 = b  in
      match uu____3549 with
      | (a,imp) ->
          let n =
            let uu____3557 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____3557
            then FStar_Util.JsonNull
            else
              (let uu____3562 =
                 let uu____3564 = nm_to_string a  in
                 imp_to_string uu____3564 imp  in
               FStar_Util.JsonStr uu____3562)
             in
          let t =
            let uu____3567 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____3567  in
          FStar_Util.JsonAssoc [("name", n); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____3599 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____3599
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____3617 = FStar_Options.print_universes ()  in
    if uu____3617 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____3633 =
      let uu____3635 = FStar_Options.ugly ()  in Prims.op_Negation uu____3635
       in
    if uu____3633
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.of_int (100)) d1
    else
      (let uu____3645 = s  in
       match uu____3645 with
       | (us,t) ->
           let uu____3657 =
             let uu____3659 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____3659  in
           let uu____3663 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____3657 uu____3663)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____3673 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____3675 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____3678 =
      let uu____3680 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____3680  in
    let uu____3684 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____3686 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____3673 uu____3675 uu____3678
      uu____3684 uu____3686
  
let (wp_eff_combinators_to_string :
  FStar_Syntax_Syntax.wp_eff_combinators -> Prims.string) =
  fun combs  ->
    let tscheme_opt_to_string uu___13_3704 =
      match uu___13_3704 with
      | FStar_Pervasives_Native.Some ts -> tscheme_to_string ts
      | FStar_Pervasives_Native.None  -> "None"  in
    let uu____3710 =
      let uu____3714 = tscheme_to_string combs.FStar_Syntax_Syntax.ret_wp  in
      let uu____3716 =
        let uu____3720 = tscheme_to_string combs.FStar_Syntax_Syntax.bind_wp
           in
        let uu____3722 =
          let uu____3726 =
            tscheme_to_string combs.FStar_Syntax_Syntax.stronger  in
          let uu____3728 =
            let uu____3732 =
              tscheme_to_string combs.FStar_Syntax_Syntax.if_then_else  in
            let uu____3734 =
              let uu____3738 =
                tscheme_to_string combs.FStar_Syntax_Syntax.ite_wp  in
              let uu____3740 =
                let uu____3744 =
                  tscheme_to_string combs.FStar_Syntax_Syntax.close_wp  in
                let uu____3746 =
                  let uu____3750 =
                    tscheme_to_string combs.FStar_Syntax_Syntax.trivial  in
                  let uu____3752 =
                    let uu____3756 =
                      tscheme_opt_to_string combs.FStar_Syntax_Syntax.repr
                       in
                    let uu____3758 =
                      let uu____3762 =
                        tscheme_opt_to_string
                          combs.FStar_Syntax_Syntax.return_repr
                         in
                      let uu____3764 =
                        let uu____3768 =
                          tscheme_opt_to_string
                            combs.FStar_Syntax_Syntax.bind_repr
                           in
                        [uu____3768]  in
                      uu____3762 :: uu____3764  in
                    uu____3756 :: uu____3758  in
                  uu____3750 :: uu____3752  in
                uu____3744 :: uu____3746  in
              uu____3738 :: uu____3740  in
            uu____3732 :: uu____3734  in
          uu____3726 :: uu____3728  in
        uu____3720 :: uu____3722  in
      uu____3714 :: uu____3716  in
    FStar_Util.format
      "{\nret_wp       = %s\n; bind_wp      = %s\n; stronger     = %s\n; if_then_else = %s\n; ite_wp       = %s\n; close_wp     = %s\n; trivial      = %s\n; repr         = %s\n; return_repr  = %s\n; bind_repr    = %s\n}\n"
      uu____3710
  
let (layered_eff_combinators_to_string :
  FStar_Syntax_Syntax.layered_eff_combinators -> Prims.string) =
  fun combs  ->
    let to_str uu____3799 =
      match uu____3799 with
      | (ts_t,ts_ty) ->
          let uu____3807 = tscheme_to_string ts_t  in
          let uu____3809 = tscheme_to_string ts_ty  in
          FStar_Util.format2 "(%s) : (%s)" uu____3807 uu____3809
       in
    let uu____3812 =
      let uu____3816 =
        FStar_Ident.string_of_lid combs.FStar_Syntax_Syntax.l_base_effect  in
      let uu____3818 =
        let uu____3822 = to_str combs.FStar_Syntax_Syntax.l_repr  in
        let uu____3824 =
          let uu____3828 = to_str combs.FStar_Syntax_Syntax.l_return  in
          let uu____3830 =
            let uu____3834 = to_str combs.FStar_Syntax_Syntax.l_bind  in
            let uu____3836 =
              let uu____3840 = to_str combs.FStar_Syntax_Syntax.l_subcomp  in
              let uu____3842 =
                let uu____3846 =
                  to_str combs.FStar_Syntax_Syntax.l_if_then_else  in
                [uu____3846]  in
              uu____3840 :: uu____3842  in
            uu____3834 :: uu____3836  in
          uu____3828 :: uu____3830  in
        uu____3822 :: uu____3824  in
      uu____3816 :: uu____3818  in
    FStar_Util.format
      "{\nl_base_effect = %s\n; l_repr = %s\n; l_return = %s\n; l_bind = %s\n; l_subcomp = %s\n; l_if_then_else = %s\n\n  }\n"
      uu____3812
  
let (eff_combinators_to_string :
  FStar_Syntax_Syntax.eff_combinators -> Prims.string) =
  fun uu___14_3862  ->
    match uu___14_3862 with
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
          let uu____3895 =
            let uu____3897 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____3897  in
          if uu____3895
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.of_int (100)) d1
          else
            (let actions_to_string actions =
               let uu____3918 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____3918 (FStar_String.concat ",\n\t")
                in
             let eff_name =
               let uu____3935 = FStar_Syntax_Util.is_layered ed  in
               if uu____3935 then "layered_effect" else "new_effect"  in
             let uu____3943 =
               let uu____3947 =
                 let uu____3951 =
                   let uu____3955 =
                     lid_to_string ed.FStar_Syntax_Syntax.mname  in
                   let uu____3957 =
                     let uu____3961 =
                       let uu____3963 =
                         univ_names_to_string ed.FStar_Syntax_Syntax.univs
                          in
                       FStar_All.pipe_left enclose_universes uu____3963  in
                     let uu____3967 =
                       let uu____3971 =
                         binders_to_string " " ed.FStar_Syntax_Syntax.binders
                          in
                       let uu____3974 =
                         let uu____3978 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.signature
                            in
                         let uu____3980 =
                           let uu____3984 =
                             eff_combinators_to_string
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____3986 =
                             let uu____3990 =
                               actions_to_string
                                 ed.FStar_Syntax_Syntax.actions
                                in
                             [uu____3990]  in
                           uu____3984 :: uu____3986  in
                         uu____3978 :: uu____3980  in
                       uu____3971 :: uu____3974  in
                     uu____3961 :: uu____3967  in
                   uu____3955 :: uu____3957  in
                 (if for_free then "_for_free " else "") :: uu____3951  in
               eff_name :: uu____3947  in
             FStar_Util.format
               "%s%s { %s%s %s : %s \n  %s\nand effect_actions\n\t%s\n}\n"
               uu____3943)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let (sub_eff_to_string : FStar_Syntax_Syntax.sub_eff -> Prims.string) =
  fun se  ->
    let tsopt_to_string ts_opt =
      if FStar_Util.is_some ts_opt
      then
        let uu____4042 = FStar_All.pipe_right ts_opt FStar_Util.must  in
        FStar_All.pipe_right uu____4042 tscheme_to_string
      else "<None>"  in
    let uu____4049 = lid_to_string se.FStar_Syntax_Syntax.source  in
    let uu____4051 = lid_to_string se.FStar_Syntax_Syntax.target  in
    let uu____4053 = tsopt_to_string se.FStar_Syntax_Syntax.lift  in
    let uu____4055 = tsopt_to_string se.FStar_Syntax_Syntax.lift_wp  in
    FStar_Util.format4 "sub_effect %s ~> %s : lift = %s ;; lift_wp = %s"
      uu____4049 uu____4051 uu____4053 uu____4055
  
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
          (lid,univs,tps,k,uu____4090,uu____4091) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____4107 = FStar_Options.print_universes ()  in
          if uu____4107
          then
            let uu____4111 = FStar_Ident.string_of_lid lid  in
            let uu____4113 = univ_names_to_string univs  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str uu____4111
              uu____4113 binders_str term_str
          else
            (let uu____4118 = FStar_Ident.string_of_lid lid  in
             FStar_Util.format4 "%stype %s %s : %s" quals_str uu____4118
               binders_str term_str)
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs,t,uu____4124,uu____4125,uu____4126) ->
          let uu____4133 = FStar_Options.print_universes ()  in
          if uu____4133
          then
            let uu____4137 = univ_names_to_string univs  in
            let uu____4139 = FStar_Ident.string_of_lid lid  in
            let uu____4141 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____4137 uu____4139
              uu____4141
          else
            (let uu____4146 = FStar_Ident.string_of_lid lid  in
             let uu____4148 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" uu____4146 uu____4148)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs,t) ->
          let uu____4154 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____4156 = FStar_Ident.string_of_lid lid  in
          let uu____4158 =
            let uu____4160 = FStar_Options.print_universes ()  in
            if uu____4160
            then
              let uu____4164 = univ_names_to_string univs  in
              FStar_Util.format1 "<%s>" uu____4164
            else ""  in
          let uu____4170 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____4154 uu____4156
            uu____4158 uu____4170
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____4176 = FStar_Options.print_universes ()  in
          if uu____4176
          then
            let uu____4180 = FStar_Ident.string_of_lid lid  in
            let uu____4182 = univ_names_to_string us  in
            let uu____4184 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" uu____4180 uu____4182
              uu____4184
          else
            (let uu____4189 = FStar_Ident.string_of_lid lid  in
             let uu____4191 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" uu____4189 uu____4191)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____4195) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____4201) ->
          let uu____4210 =
            let uu____4212 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4212 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____4210
      | FStar_Syntax_Syntax.Sig_fail (errs,lax,ses) ->
          let uu____4238 = FStar_Util.string_of_bool lax  in
          let uu____4240 =
            FStar_Common.string_of_list FStar_Util.string_of_int errs  in
          let uu____4243 =
            let uu____4245 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____4245 (FStar_String.concat "\n")  in
          FStar_Util.format3 "(* Sig_fail %s %s *)\n%s\n(* / Sig_fail*)\n"
            uu____4238 uu____4240 uu____4243
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4257 = FStar_Syntax_Util.is_dm4f ed  in
          eff_decl_to_string' uu____4257 x.FStar_Syntax_Syntax.sigrng
            x.FStar_Syntax_Syntax.sigquals ed
      | FStar_Syntax_Syntax.Sig_sub_effect se -> sub_eff_to_string se
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs,tps,c,flags) ->
          let uu____4269 = FStar_Options.print_universes ()  in
          if uu____4269
          then
            let uu____4273 =
              let uu____4278 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs uu____4278  in
            (match uu____4273 with
             | (univs1,t) ->
                 let uu____4292 =
                   let uu____4297 =
                     let uu____4298 = FStar_Syntax_Subst.compress t  in
                     uu____4298.FStar_Syntax_Syntax.n  in
                   match uu____4297 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____4327 -> failwith "impossible"  in
                 (match uu____4292 with
                  | (tps1,c1) ->
                      let uu____4336 = sli l  in
                      let uu____4338 = univ_names_to_string univs1  in
                      let uu____4340 = binders_to_string " " tps1  in
                      let uu____4343 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____4336
                        uu____4338 uu____4340 uu____4343))
          else
            (let uu____4348 = sli l  in
             let uu____4350 = binders_to_string " " tps  in
             let uu____4353 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____4348 uu____4350
               uu____4353)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____4362 =
            let uu____4364 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____4364  in
          let uu____4374 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____4362 uu____4374
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,t,ty) ->
          let uu____4382 = FStar_Ident.string_of_lid m  in
          let uu____4384 = FStar_Ident.string_of_lid n  in
          let uu____4386 = FStar_Ident.string_of_lid p  in
          let uu____4388 = tscheme_to_string t  in
          let uu____4390 = tscheme_to_string ty  in
          FStar_Util.format5 "polymonadic_bind (%s, %s) |> %s = (%s, %s)"
            uu____4382 uu____4384 uu____4386 uu____4388 uu____4390
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> Prims.op_Hat "[@ ]" (Prims.op_Hat "\n" basic)
    | uu____4396 ->
        let uu____4399 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____4399 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____4416 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____4416 msg
  
let (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____4427,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____4429;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____4431;
                       FStar_Syntax_Syntax.lbdef = uu____4432;
                       FStar_Syntax_Syntax.lbattrs = uu____4433;
                       FStar_Syntax_Syntax.lbpos = uu____4434;_}::[]),uu____4435)
        ->
        let uu____4458 = lbname_to_string lb  in
        let uu____4460 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____4458 uu____4460
    | uu____4463 ->
        let uu____4464 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> FStar_Ident.string_of_lid l))
           in
        FStar_All.pipe_right uu____4464 (FStar_String.concat ", ")
  
let (tag_of_sigelt : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____4490 -> "Sig_inductive_typ"
    | FStar_Syntax_Syntax.Sig_bundle uu____4508 -> "Sig_bundle"
    | FStar_Syntax_Syntax.Sig_datacon uu____4518 -> "Sig_datacon"
    | FStar_Syntax_Syntax.Sig_declare_typ uu____4535 -> "Sig_declare_typ"
    | FStar_Syntax_Syntax.Sig_let uu____4543 -> "Sig_let"
    | FStar_Syntax_Syntax.Sig_assume uu____4551 -> "Sig_assume"
    | FStar_Syntax_Syntax.Sig_new_effect uu____4559 -> "Sig_new_effect"
    | FStar_Syntax_Syntax.Sig_sub_effect uu____4561 -> "Sig_sub_effect"
    | FStar_Syntax_Syntax.Sig_effect_abbrev uu____4563 -> "Sig_effect_abbrev"
    | FStar_Syntax_Syntax.Sig_pragma uu____4577 -> "Sig_pragma"
    | FStar_Syntax_Syntax.Sig_splice uu____4579 -> "Sig_splice"
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____4587 ->
        "Sig_polymonadic_bind"
    | FStar_Syntax_Syntax.Sig_fail uu____4599 -> "Sig_fail"
  
let (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____4620 = sli m.FStar_Syntax_Syntax.name  in
    let uu____4622 =
      let uu____4624 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____4624 (FStar_String.concat "\n")  in
    let uu____4634 =
      let uu____4636 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____4636 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____4620
      uu____4622 uu____4634
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          (FStar_Util.string_builder_append strb "[";
           (let uu____4686 = f x  in
            FStar_Util.string_builder_append strb uu____4686);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____4695 = f x1  in
                 FStar_Util.string_builder_append strb uu____4695)) xs;
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
           (let uu____4742 = f x  in
            FStar_Util.string_builder_append strb uu____4742);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____4751 = f x1  in
                 FStar_Util.string_builder_append strb uu____4751)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____4773 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____4773
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___15_4786  ->
    match uu___15_4786 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____4802 =
          let uu____4804 =
            let uu____4806 =
              let uu____4808 =
                let uu____4810 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____4810 (FStar_String.concat " ")  in
              Prims.op_Hat uu____4808 ")"  in
            Prims.op_Hat " " uu____4806  in
          Prims.op_Hat h uu____4804  in
        Prims.op_Hat "(" uu____4802
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____4825 =
          let uu____4827 = emb_typ_to_string a  in
          let uu____4829 =
            let uu____4831 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____4831  in
          Prims.op_Hat uu____4827 uu____4829  in
        Prims.op_Hat "(" uu____4825
  