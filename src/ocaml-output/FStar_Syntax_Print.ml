open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___429_56143  ->
    match uu___429_56143 with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        let uu____56147 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_constant_at_level " uu____56147
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        let uu____56152 = FStar_Util.string_of_int i  in
        Prims.op_Hat "Delta_equational_at_level " uu____56152
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____56156 =
          let uu____56158 = delta_depth_to_string d  in
          Prims.op_Hat uu____56158 ")"  in
        Prims.op_Hat "Delta_abstract (" uu____56156
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____56170 = FStar_Options.print_real_names ()  in
    if uu____56170
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56197 =
      let uu____56199 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "#" uu____56199  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56197
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56209 = FStar_Options.print_real_names ()  in
    if uu____56209
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____56222 =
      let uu____56224 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.op_Hat "@" uu____56224  in
    Prims.op_Hat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
      uu____56222
  
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
      | uu____56446 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____56459 -> failwith "get_lid"
  
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
  'Auu____56562 'Auu____56563 .
    ('Auu____56562,'Auu____56563) FStar_Util.either -> Prims.bool
  =
  fun uu___430_56573  ->
    match uu___430_56573 with
    | FStar_Util.Inl uu____56578 -> false
    | FStar_Util.Inr uu____56580 -> true
  
let filter_imp :
  'Auu____56587 .
    ('Auu____56587 * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      ('Auu____56587 * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___431_56642  ->
            match uu___431_56642 with
            | (uu____56650,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta t)) when
                FStar_Syntax_Util.is_fvar FStar_Parser_Const.tcresolve_lid t
                -> true
            | (uu____56657,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____56658)) -> false
            | (uu____56663,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Meta uu____56664)) -> false
            | uu____56670 -> true))
  
let rec (reconstruct_lex :
  exp -> exp Prims.list FStar_Pervasives_Native.option) =
  fun e  ->
    let uu____56688 =
      let uu____56689 = FStar_Syntax_Subst.compress e  in
      uu____56689.FStar_Syntax_Syntax.n  in
    match uu____56688 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____56750 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____56750
        then
          let uu____56759 =
            let uu____56764 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____56764  in
          (match uu____56759 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____56775 =
                 let uu____56778 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____56778 :: xs  in
               FStar_Pervasives_Native.Some uu____56775
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____56790 ->
        let uu____56791 = is_lex_top e  in
        if uu____56791
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____56839 = f hd1  in if uu____56839 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident * Prims.string) Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____56871 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____56871
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56902 = get_lid e  in find_lid uu____56902 infix_prim_ops
  
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  ->
    let uu____56914 = get_lid e  in find_lid uu____56914 unary_prim_ops
  
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____56926 = get_lid t  in find_lid uu____56926 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___432_56940  ->
    match uu___432_56940 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____56951 = FStar_Options.hide_uvar_nums ()  in
    if uu____56951
    then "?"
    else
      (let uu____56958 =
         let uu____56960 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____56960 FStar_Util.string_of_int  in
       Prims.op_Hat "?" uu____56958)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____56972 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major
       in
    let uu____56974 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor
       in
    FStar_Util.format2 "%s.%s" uu____56972 uu____56974
  
let (univ_uvar_to_string :
  (FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.p_uvar * FStar_Syntax_Syntax.version) -> Prims.string)
  =
  fun u  ->
    let uu____57000 = FStar_Options.hide_uvar_nums ()  in
    if uu____57000
    then "?"
    else
      (let uu____57007 =
         let uu____57009 =
           let uu____57011 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____57011 FStar_Util.string_of_int  in
         let uu____57015 =
           let uu____57017 =
             version_to_string (FStar_Pervasives_Native.snd u)  in
           Prims.op_Hat ":" uu____57017  in
         Prims.op_Hat uu____57009 uu____57015  in
       Prims.op_Hat "?" uu____57007)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int * FStar_Syntax_Syntax.universe
        FStar_Pervasives_Native.option))
  =
  fun n1  ->
    fun u  ->
      let uu____57045 = FStar_Syntax_Subst.compress_univ u  in
      match uu____57045 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____57058 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____57069 = FStar_Syntax_Subst.compress_univ u  in
    match uu____57069 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____57080 = univ_uvar_to_string u1  in
        Prims.op_Hat "U_unif " uu____57080
    | FStar_Syntax_Syntax.U_name x ->
        Prims.op_Hat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____57087 = FStar_Util.string_of_int x  in
        Prims.op_Hat "@" uu____57087
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____57092 = int_of_univ (Prims.parse_int "1") u1  in
        (match uu____57092 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____57113 = univ_to_string u2  in
             let uu____57115 = FStar_Util.string_of_int n1  in
             FStar_Util.format2 "(%s + %s)" uu____57113 uu____57115)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____57121 =
          let uu____57123 = FStar_List.map univ_to_string us  in
          FStar_All.pipe_right uu____57123 (FStar_String.concat ", ")  in
        FStar_Util.format1 "(max %s)" uu____57121
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
  
let (univs_to_string : FStar_Syntax_Syntax.universes -> Prims.string) =
  fun us  ->
    let uu____57142 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____57142 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____57159 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____57159 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___433_57177  ->
    match uu___433_57177 with
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
        let uu____57193 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____57193
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____57198 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____57198
          x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____57211 =
          let uu____57213 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57213  in
        let uu____57214 =
          let uu____57216 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57216 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____57211 uu____57214
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____57242 =
          let uu____57244 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____57244  in
        let uu____57245 =
          let uu____57247 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____57247 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____57242
          uu____57245
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____57264 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____57264
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
    | uu____57287 ->
        let uu____57290 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____57290 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____57318 ->
        let uu____57321 = quals_to_string quals  in
        Prims.op_Hat uu____57321 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.op_Hat "(" (Prims.op_Hat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____57517 = db_to_string x  in
        Prims.op_Hat "Tm_bvar: " uu____57517
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____57521 = nm_to_string x  in
        Prims.op_Hat "Tm_name: " uu____57521
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____57525 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.op_Hat "Tm_fvar: " uu____57525
    | FStar_Syntax_Syntax.Tm_uinst uu____57528 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____57536 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____57538 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57540,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_static ;
                       FStar_Syntax_Syntax.antiquotes = uu____57541;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____57555,{
                       FStar_Syntax_Syntax.qkind =
                         FStar_Syntax_Syntax.Quote_dynamic ;
                       FStar_Syntax_Syntax.antiquotes = uu____57556;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____57570 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____57590 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____57606 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____57614 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____57632 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____57656 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____57684 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____57699 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____57713,m) ->
        let uu____57751 = FStar_ST.op_Bang m  in
        (match uu____57751 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____57809 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____57815,m) ->
        let uu____57821 = metadata_to_string m  in
        Prims.op_Hat "Tm_meta:" uu____57821
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____57825 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____57828 =
      let uu____57830 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____57830  in
    if uu____57828
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____57844 = FStar_Options.print_implicits ()  in
         if uu____57844 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____57852 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____57877,[]) ->
           failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = b;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               (uu____57903,thunk1);
             FStar_Syntax_Syntax.ltyp = uu____57905;
             FStar_Syntax_Syntax.rng = uu____57906;_}
           ->
           let uu____57917 =
             let uu____57919 =
               let uu____57921 = FStar_Common.force_thunk thunk1  in
               term_to_string uu____57921  in
             Prims.op_Hat uu____57919 "]"  in
           Prims.op_Hat "[LAZYEMB:" uu____57917
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____57967 =
             let uu____57969 =
               let uu____57971 =
                 let uu____57972 =
                   let uu____57981 =
                     FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
                   FStar_Util.must uu____57981  in
                 uu____57972 i.FStar_Syntax_Syntax.lkind i  in
               term_to_string uu____57971  in
             Prims.op_Hat uu____57969 "]"  in
           Prims.op_Hat "[lazy:" uu____57967
       | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  ->
                let print_aq uu____58050 =
                  match uu____58050 with
                  | (bv,t) ->
                      let uu____58058 = bv_to_string bv  in
                      let uu____58060 = term_to_string t  in
                      FStar_Util.format2 "%s -> %s" uu____58058 uu____58060
                   in
                let uu____58063 = term_to_string tm  in
                let uu____58065 =
                  FStar_Common.string_of_list print_aq
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                FStar_Util.format2 "`(%s)%s" uu____58063 uu____58065
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let uu____58074 = term_to_string tm  in
                FStar_Util.format1 "quote (%s)" uu____58074)
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____58097 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____58134 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____58159  ->
                                 match uu____58159 with
                                 | (t1,uu____58168) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____58134
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____58097 (FStar_String.concat "\\/")  in
           let uu____58183 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____58183
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____58197 = tag_of_term t  in
           let uu____58199 = sli m  in
           let uu____58201 = term_to_string t'  in
           let uu____58203 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____58197
             uu____58199 uu____58201 uu____58203
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____58218 = tag_of_term t  in
           let uu____58220 = term_to_string t'  in
           let uu____58222 = sli m0  in
           let uu____58224 = sli m1  in
           let uu____58226 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)"
             uu____58218 uu____58220 uu____58222 uu____58224 uu____58226
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____58241 = FStar_Range.string_of_range r  in
           let uu____58243 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____58241
             uu____58243
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____58252 = lid_to_string l  in
           let uu____58254 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____58256 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____58252
             uu____58254 uu____58256
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____58260) ->
           let uu____58265 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____58265
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____58269 = db_to_string x3  in
           let uu____58271 =
             let uu____58273 =
               let uu____58275 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.op_Hat uu____58275 ")"  in
             Prims.op_Hat ":(" uu____58273  in
           Prims.op_Hat uu____58269 uu____58271
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,([],uu____58282)) ->
           let uu____58297 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58297
           then ctx_uvar_to_string u
           else
             (let uu____58303 =
                let uu____58305 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58305  in
              Prims.op_Hat "?" uu____58303)
       | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
           let uu____58328 =
             (FStar_Options.print_bound_var_types ()) &&
               (FStar_Options.print_effect_args ())
              in
           if uu____58328
           then
             let uu____58332 = ctx_uvar_to_string u  in
             let uu____58334 =
               let uu____58336 =
                 FStar_List.map subst_to_string
                   (FStar_Pervasives_Native.fst s)
                  in
               FStar_All.pipe_right uu____58336 (FStar_String.concat "; ")
                in
             FStar_Util.format2 "(%s @ %s)" uu____58332 uu____58334
           else
             (let uu____58355 =
                let uu____58357 =
                  FStar_Syntax_Unionfind.uvar_id
                    u.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                FStar_All.pipe_left FStar_Util.string_of_int uu____58357  in
              Prims.op_Hat "?" uu____58355)
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____58364 = FStar_Options.print_universes ()  in
           if uu____58364
           then
             let uu____58368 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____58368
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____58396 = binders_to_string " -> " bs  in
           let uu____58399 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____58396 uu____58399
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____58431 = binders_to_string " " bs  in
                let uu____58434 = term_to_string t2  in
                let uu____58436 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____58445 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____58445)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____58431 uu____58434
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____58436
            | uu____58449 ->
                let uu____58452 = binders_to_string " " bs  in
                let uu____58455 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____58452 uu____58455)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____58464 = bv_to_string xt  in
           let uu____58466 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____58469 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____58464 uu____58466
             uu____58469
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____58501 = term_to_string t  in
           let uu____58503 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____58501 uu____58503
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____58526 = lbs_to_string [] lbs  in
           let uu____58528 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____58526 uu____58528
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____58593 =
                   let uu____58595 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____58595
                     (FStar_Util.dflt "default")
                    in
                 let uu____58606 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____58593 uu____58606
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____58627 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____58627
              in
           let uu____58630 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____58630 annot1
             topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____58671 = term_to_string head1  in
           let uu____58673 =
             let uu____58675 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____58708  ->
                       match uu____58708 with
                       | (p,wopt,e) ->
                           let uu____58725 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____58728 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____58733 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____58733
                              in
                           let uu____58737 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____58725
                             uu____58728 uu____58737))
                in
             FStar_Util.concat_l "\n\t|" uu____58675  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____58671
             uu____58673
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____58749 = FStar_Options.print_universes ()  in
           if uu____58749
           then
             let uu____58753 = term_to_string t  in
             let uu____58755 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____58753 uu____58755
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (ctx_uvar_to_string : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  ->
    let uu____58762 =
      binders_to_string ", " ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_binders
       in
    let uu____58765 =
      uvar_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head  in
    let uu____58767 =
      term_to_string ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_typ  in
    FStar_Util.format4 "(* %s *)\n(%s |- %s : %s)"
      ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_reason uu____58762 uu____58765
      uu____58767

and (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___434_58770  ->
    match uu___434_58770 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____58776 = FStar_Util.string_of_int i  in
        let uu____58778 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____58776 uu____58778
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____58785 = bv_to_string x  in
        let uu____58787 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____58785 uu____58787
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____58796 = bv_to_string x  in
        let uu____58798 = term_to_string t  in
        FStar_Util.format2 "NT (%s, %s)" uu____58796 uu____58798
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____58805 = FStar_Util.string_of_int i  in
        let uu____58807 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____58805 uu____58807
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____58814 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____58814

and (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____58818 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____58818 (FStar_String.concat "; ")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____58834 =
      let uu____58836 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____58836  in
    if uu____58834
    then
      let e =
        let uu____58841 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____58841  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____58870 = fv_to_string l  in
           let uu____58872 =
             let uu____58874 =
               FStar_List.map
                 (fun uu____58888  ->
                    match uu____58888 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.op_Hat "#" p else p) pats
                in
             FStar_All.pipe_right uu____58874 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____58870 uu____58872
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____58913) ->
           let uu____58918 = FStar_Options.print_bound_var_types ()  in
           if uu____58918
           then
             let uu____58922 = bv_to_string x1  in
             let uu____58924 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____58922 uu____58924
           else
             (let uu____58929 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____58929)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____58933 = FStar_Options.print_bound_var_types ()  in
           if uu____58933
           then
             let uu____58937 = bv_to_string x1  in
             let uu____58939 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____58937 uu____58939
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____58946 = FStar_Options.print_bound_var_types ()  in
           if uu____58946
           then
             let uu____58950 = bv_to_string x1  in
             let uu____58952 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "_wild_%s:%s" uu____58950 uu____58952
           else bv_to_string x1)

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.letbindings -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____58961 = quals_to_string' quals  in
      let uu____58963 =
        let uu____58965 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____58985 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____58987 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____58989 =
                    let uu____58991 = FStar_Options.print_universes ()  in
                    if uu____58991
                    then
                      let uu____58995 =
                        let uu____58997 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.op_Hat uu____58997 ">"  in
                      Prims.op_Hat "<" uu____58995
                    else ""  in
                  let uu____59004 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____59006 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____58985
                    uu____58987 uu____58989 uu____59004 uu____59006))
           in
        FStar_Util.concat_l "\n and " uu____58965  in
      FStar_Util.format3 "%slet %s %s" uu____58961
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____58963

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___435_59021  ->
    match uu___435_59021 with
    | [] -> ""
    | tms ->
        let uu____59029 =
          let uu____59031 =
            FStar_List.map
              (fun t  ->
                 let uu____59039 = term_to_string t  in paren uu____59039)
              tms
             in
          FStar_All.pipe_right uu____59031 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____59029

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____59048 = FStar_Options.print_effect_args ()  in
    if uu____59048
    then
      let uu____59052 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____59052
    else
      (let uu____59055 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____59057 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____59055 uu____59057)

and (aqual_to_string' :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string)
  =
  fun s  ->
    fun uu___436_59061  ->
      match uu___436_59061 with
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
          let uu____59079 =
            let uu____59081 = term_to_string t  in
            Prims.op_Hat uu____59081 (Prims.op_Hat "]" s)  in
          Prims.op_Hat "#[" uu____59079
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
      let uu____59101 =
        let uu____59103 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____59103  in
      if uu____59101
      then
        let uu____59107 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____59107 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____59118 = b  in
         match uu____59118 with
         | (a,imp) ->
             let uu____59132 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____59132
             then
               let uu____59136 = term_to_string a.FStar_Syntax_Syntax.sort
                  in
               Prims.op_Hat "_:" uu____59136
             else
               (let uu____59141 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____59144 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____59144)
                   in
                if uu____59141
                then
                  let uu____59148 = nm_to_string a  in
                  imp_to_string uu____59148 imp
                else
                  (let uu____59152 =
                     let uu____59154 = nm_to_string a  in
                     let uu____59156 =
                       let uu____59158 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.op_Hat ":" uu____59158  in
                     Prims.op_Hat uu____59154 uu____59156  in
                   imp_to_string uu____59152 imp)))

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
        let uu____59177 = FStar_Options.print_implicits ()  in
        if uu____59177 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____59188 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____59188 (FStar_String.concat sep)
      else
        (let uu____59216 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____59216 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) -> Prims.string)
  =
  fun uu___437_59230  ->
    match uu___437_59230 with
    | (a,imp) ->
        let uu____59244 = term_to_string a  in imp_to_string uu____59244 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____59256 = FStar_Options.print_implicits ()  in
      if uu____59256 then args else filter_imp args  in
    let uu____59271 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59271 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____59300 = FStar_Options.ugly ()  in
      if uu____59300
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____59311 =
      let uu____59313 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59313  in
    if uu____59311
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____59334 =
             let uu____59335 = FStar_Syntax_Subst.compress t  in
             uu____59335.FStar_Syntax_Syntax.n  in
           (match uu____59334 with
            | FStar_Syntax_Syntax.Tm_type uu____59339 when
                let uu____59340 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59340 -> term_to_string t
            | uu____59342 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59345 = univ_to_string u  in
                     let uu____59347 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____59345 uu____59347
                 | uu____59350 ->
                     let uu____59353 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____59353))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____59366 =
             let uu____59367 = FStar_Syntax_Subst.compress t  in
             uu____59367.FStar_Syntax_Syntax.n  in
           (match uu____59366 with
            | FStar_Syntax_Syntax.Tm_type uu____59371 when
                let uu____59372 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____59372 -> term_to_string t
            | uu____59374 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____59377 = univ_to_string u  in
                     let uu____59379 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____59377 uu____59379
                 | uu____59382 ->
                     let uu____59385 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____59385))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____59391 = FStar_Options.print_effect_args ()  in
             if uu____59391
             then
               let uu____59395 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____59397 =
                 let uu____59399 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____59399 (FStar_String.concat ", ")
                  in
               let uu____59414 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____59416 =
                 let uu____59418 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____59418 (FStar_String.concat ", ")
                  in
               let uu____59445 =
                 cflags_to_string c1.FStar_Syntax_Syntax.flags  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)"
                 uu____59395 uu____59397 uu____59414 uu____59416 uu____59445
             else
               (let uu____59450 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___438_59456  ->
                           match uu___438_59456 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____59459 -> false)))
                    &&
                    (let uu____59462 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____59462)
                   in
                if uu____59450
                then
                  let uu____59466 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____59466
                else
                  (let uu____59471 =
                     ((let uu____59475 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____59475) &&
                        (let uu____59478 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____59478))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____59471
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____59484 =
                        (let uu____59488 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____59488) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___439_59494  ->
                                   match uu___439_59494 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____59497 -> false)))
                         in
                      if uu____59484
                      then
                        let uu____59501 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____59501
                      else
                        (let uu____59506 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____59508 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____59506 uu____59508))))
              in
           let dec =
             let uu____59513 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___440_59526  ->
                       match uu___440_59526 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____59533 =
                             let uu____59535 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____59535
                              in
                           [uu____59533]
                       | uu____59540 -> []))
                in
             FStar_All.pipe_right uu____59513 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____59559 -> ""

and (cflags_to_string : FStar_Syntax_Syntax.cflag Prims.list -> Prims.string)
  = fun fs  -> FStar_Common.string_of_list cflag_to_string fs

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___441_59569  ->
    match uu___441_59569 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____59586 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____59623 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____59648  ->
                              match uu____59648 with
                              | (t,uu____59657) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____59623
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____59586 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____59674 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____59674
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____59679) ->
        let uu____59684 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____59684
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____59695 = sli m  in
        let uu____59697 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____59695 uu____59697
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____59707 = sli m  in
        let uu____59709 = sli m'  in
        let uu____59711 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____59707
          uu____59709 uu____59711

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____59726 = FStar_Options.ugly ()  in
      if uu____59726
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
      let uu____59747 = b  in
      match uu____59747 with
      | (a,imp) ->
          let n1 =
            let uu____59755 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____59755
            then FStar_Util.JsonNull
            else
              (let uu____59760 =
                 let uu____59762 = nm_to_string a  in
                 imp_to_string uu____59762 imp  in
               FStar_Util.JsonStr uu____59760)
             in
          let t =
            let uu____59765 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____59765  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____59797 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____59797
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____59815 = FStar_Options.print_universes ()  in
    if uu____59815 then Prims.op_Hat "<" (Prims.op_Hat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____59831 =
      let uu____59833 = FStar_Options.ugly ()  in
      Prims.op_Negation uu____59833  in
    if uu____59831
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____59843 = s  in
       match uu____59843 with
       | (us,t) ->
           let uu____59855 =
             let uu____59857 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____59857  in
           let uu____59861 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____59855 uu____59861)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____59871 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____59873 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____59876 =
      let uu____59878 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____59878  in
    let uu____59882 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____59884 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____59871 uu____59873
      uu____59876 uu____59882 uu____59884
  
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
          let uu____59915 =
            let uu____59917 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____59917  in
          if uu____59915
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____59938 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____59938 (FStar_String.concat ",\n\t")
                in
             let uu____59953 =
               let uu____59957 =
                 let uu____59961 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____59963 =
                   let uu____59967 =
                     let uu____59969 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____59969  in
                   let uu____59973 =
                     let uu____59977 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____59980 =
                       let uu____59984 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____59986 =
                         let uu____59990 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____59992 =
                           let uu____59996 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____59998 =
                             let uu____60002 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____60004 =
                               let uu____60008 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____60010 =
                                 let uu____60014 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____60016 =
                                   let uu____60020 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____60022 =
                                     let uu____60026 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____60028 =
                                       let uu____60032 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____60034 =
                                         let uu____60038 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____60040 =
                                           let uu____60044 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____60046 =
                                             let uu____60050 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____60052 =
                                               let uu____60056 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____60058 =
                                                 let uu____60062 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____60064 =
                                                   let uu____60068 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____60068]  in
                                                 uu____60062 :: uu____60064
                                                  in
                                               uu____60056 :: uu____60058  in
                                             uu____60050 :: uu____60052  in
                                           uu____60044 :: uu____60046  in
                                         uu____60038 :: uu____60040  in
                                       uu____60032 :: uu____60034  in
                                     uu____60026 :: uu____60028  in
                                   uu____60020 :: uu____60022  in
                                 uu____60014 :: uu____60016  in
                               uu____60008 :: uu____60010  in
                             uu____60002 :: uu____60004  in
                           uu____59996 :: uu____59998  in
                         uu____59990 :: uu____59992  in
                       uu____59984 :: uu____59986  in
                     uu____59977 :: uu____59980  in
                   uu____59967 :: uu____59973  in
                 uu____59961 :: uu____59963  in
               (if for_free then "_for_free " else "") :: uu____59957  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____59953)
  
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
          (lid,univs1,tps,k,uu____60142,uu____60143) ->
          let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
          let binders_str = binders_to_string " " tps  in
          let term_str = term_to_string k  in
          let uu____60159 = FStar_Options.print_universes ()  in
          if uu____60159
          then
            let uu____60163 = univ_names_to_string univs1  in
            FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
              lid.FStar_Ident.str uu____60163 binders_str term_str
          else
            FStar_Util.format4 "%stype %s %s : %s" quals_str
              lid.FStar_Ident.str binders_str term_str
      | FStar_Syntax_Syntax.Sig_datacon
          (lid,univs1,t,uu____60172,uu____60173,uu____60174) ->
          let uu____60181 = FStar_Options.print_universes ()  in
          if uu____60181
          then
            let uu____60185 = univ_names_to_string univs1  in
            let uu____60187 = term_to_string t  in
            FStar_Util.format3 "datacon<%s> %s : %s" uu____60185
              lid.FStar_Ident.str uu____60187
          else
            (let uu____60192 = term_to_string t  in
             FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
               uu____60192)
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
          let uu____60198 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
             in
          let uu____60200 =
            let uu____60202 = FStar_Options.print_universes ()  in
            if uu____60202
            then
              let uu____60206 = univ_names_to_string univs1  in
              FStar_Util.format1 "<%s>" uu____60206
            else ""  in
          let uu____60212 = term_to_string t  in
          FStar_Util.format4 "%sval %s %s : %s" uu____60198
            lid.FStar_Ident.str uu____60200 uu____60212
      | FStar_Syntax_Syntax.Sig_assume (lid,us,f) ->
          let uu____60218 = FStar_Options.print_universes ()  in
          if uu____60218
          then
            let uu____60222 = univ_names_to_string us  in
            let uu____60224 = term_to_string f  in
            FStar_Util.format3 "val %s<%s> : %s" lid.FStar_Ident.str
              uu____60222 uu____60224
          else
            (let uu____60229 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____60229)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____60233) ->
          lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
      | FStar_Syntax_Syntax.Sig_main e ->
          let uu____60239 = term_to_string e  in
          FStar_Util.format1 "let _ = %s" uu____60239
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____60243) ->
          let uu____60252 =
            let uu____60254 = FStar_List.map sigelt_to_string ses  in
            FStar_All.pipe_right uu____60254 (FStar_String.concat "\n")  in
          Prims.op_Hat "(* Sig_bundle *)" uu____60252
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
            | (FStar_Pervasives_Native.Some lift_wp,uu____60299) -> lift_wp
            | (uu____60306,FStar_Pervasives_Native.Some lift) -> lift  in
          let uu____60314 =
            FStar_Syntax_Subst.open_univ_vars
              (FStar_Pervasives_Native.fst lift_wp)
              (FStar_Pervasives_Native.snd lift_wp)
             in
          (match uu____60314 with
           | (us,t) ->
               let uu____60326 = lid_to_string se.FStar_Syntax_Syntax.source
                  in
               let uu____60328 = lid_to_string se.FStar_Syntax_Syntax.target
                  in
               let uu____60330 = univ_names_to_string us  in
               let uu____60332 = term_to_string t  in
               FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____60326
                 uu____60328 uu____60330 uu____60332)
      | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
          let uu____60344 = FStar_Options.print_universes ()  in
          if uu____60344
          then
            let uu____60348 =
              let uu____60353 =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
                 in
              FStar_Syntax_Subst.open_univ_vars univs1 uu____60353  in
            (match uu____60348 with
             | (univs2,t) ->
                 let uu____60367 =
                   let uu____60372 =
                     let uu____60373 = FStar_Syntax_Subst.compress t  in
                     uu____60373.FStar_Syntax_Syntax.n  in
                   match uu____60372 with
                   | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                   | uu____60402 -> failwith "impossible"  in
                 (match uu____60367 with
                  | (tps1,c1) ->
                      let uu____60411 = sli l  in
                      let uu____60413 = univ_names_to_string univs2  in
                      let uu____60415 = binders_to_string " " tps1  in
                      let uu____60418 = comp_to_string c1  in
                      FStar_Util.format4 "effect %s<%s> %s = %s" uu____60411
                        uu____60413 uu____60415 uu____60418))
          else
            (let uu____60423 = sli l  in
             let uu____60425 = binders_to_string " " tps  in
             let uu____60428 = comp_to_string c  in
             FStar_Util.format3 "effect %s %s = %s" uu____60423 uu____60425
               uu____60428)
      | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
          let uu____60437 =
            let uu____60439 = FStar_List.map FStar_Ident.string_of_lid lids
               in
            FStar_All.pipe_left (FStar_String.concat "; ") uu____60439  in
          let uu____60449 = term_to_string t  in
          FStar_Util.format2 "splice[%s] (%s)" uu____60437 uu____60449
       in
    match x.FStar_Syntax_Syntax.sigattrs with
    | [] -> basic
    | uu____60453 ->
        let uu____60456 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs  in
        Prims.op_Hat uu____60456 (Prims.op_Hat "\n" basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____60473 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____60473 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____60484,{ FStar_Syntax_Syntax.lbname = lb;
                        FStar_Syntax_Syntax.lbunivs = uu____60486;
                        FStar_Syntax_Syntax.lbtyp = t;
                        FStar_Syntax_Syntax.lbeff = uu____60488;
                        FStar_Syntax_Syntax.lbdef = uu____60489;
                        FStar_Syntax_Syntax.lbattrs = uu____60490;
                        FStar_Syntax_Syntax.lbpos = uu____60491;_}::[]),uu____60492)
        ->
        let uu____60515 = lbname_to_string lb  in
        let uu____60517 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____60515 uu____60517
    | uu____60520 ->
        let uu____60521 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____60521 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____60545 = sli m.FStar_Syntax_Syntax.name  in
    let uu____60547 =
      let uu____60549 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____60549 (FStar_String.concat "\n")  in
    let uu____60559 =
      let uu____60561 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____60561 (FStar_String.concat "\n")  in
    FStar_Util.format3
      "module %s\nDeclarations: [\n%s\n]\nExports: [\n%s\n]\n" uu____60545
      uu____60547 uu____60559
  
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
          (let uu____60605 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____60605))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____60614 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____60614)));
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
           (let uu____60655 = f x  in
            FStar_Util.string_builder_append strb uu____60655);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____60664 = f x1  in
                 FStar_Util.string_builder_append strb uu____60664)) xs;
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
           (let uu____60711 = f x  in
            FStar_Util.string_builder_append strb uu____60711);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____60720 = f x1  in
                 FStar_Util.string_builder_append strb uu____60720)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____60742 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____60742
  
let rec (emb_typ_to_string : FStar_Syntax_Syntax.emb_typ -> Prims.string) =
  fun uu___442_60755  ->
    match uu___442_60755 with
    | FStar_Syntax_Syntax.ET_abstract  -> "abstract"
    | FStar_Syntax_Syntax.ET_app (h,[]) -> h
    | FStar_Syntax_Syntax.ET_app (h,args) ->
        let uu____60771 =
          let uu____60773 =
            let uu____60775 =
              let uu____60777 =
                let uu____60779 = FStar_List.map emb_typ_to_string args  in
                FStar_All.pipe_right uu____60779 (FStar_String.concat " ")
                 in
              Prims.op_Hat uu____60777 ")"  in
            Prims.op_Hat " " uu____60775  in
          Prims.op_Hat h uu____60773  in
        Prims.op_Hat "(" uu____60771
    | FStar_Syntax_Syntax.ET_fun (a,b) ->
        let uu____60794 =
          let uu____60796 = emb_typ_to_string a  in
          let uu____60798 =
            let uu____60800 = emb_typ_to_string b  in
            Prims.op_Hat ") -> " uu____60800  in
          Prims.op_Hat uu____60796 uu____60798  in
        Prims.op_Hat "(" uu____60794
  