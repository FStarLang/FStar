open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___94_5  ->
    match uu___94_5 with
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
    let uu____30 =
      lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
       in
    let uu____31 =
      let uu____32 =
        let uu____33 = delta_depth_to_string fv.FStar_Syntax_Syntax.fv_delta
           in
        Prims.strcat uu____33 ")"  in
      Prims.strcat "(@@" uu____32  in
    Prims.strcat uu____30 uu____31
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____39 =
      let uu____40 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____40  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____39
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____46 = FStar_Options.print_real_names ()  in
    if uu____46
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____53 =
      let uu____54 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____54  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____53
  
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
      | uu____192 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____203 -> failwith "get_lid"
  
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
type exp = FStar_Syntax_Syntax.term[@@deriving show]
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
  'Auu____275 'Auu____276 .
    ('Auu____275,'Auu____276) FStar_Util.either -> Prims.bool
  =
  fun uu___95_285  ->
    match uu___95_285 with
    | FStar_Util.Inl uu____290 -> false
    | FStar_Util.Inr uu____291 -> true
  
let filter_imp :
  'Auu____296 .
    ('Auu____296,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____296,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___96_351  ->
            match uu___96_351 with
            | (uu____358,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____359)) -> false
            | uu____362 -> true))
  
let rec (reconstruct_lex :
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____380 =
      let uu____381 = FStar_Syntax_Subst.compress e  in
      uu____381.FStar_Syntax_Syntax.n  in
    match uu____380 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____444 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____444
        then
          let uu____453 =
            let uu____460 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____460  in
          (match uu____453 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____478 =
                 let uu____483 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____483 :: xs  in
               FStar_Pervasives_Native.Some uu____478
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____507 ->
        let uu____508 = is_lex_top e  in
        if uu____508
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____557 = f hd1  in if uu____557 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____581 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____581
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____605 = get_lid e  in find_lid uu____605 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____615 = get_lid e  in find_lid uu____615 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____625 = get_lid t  in find_lid uu____625 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___97_635  ->
    match uu___97_635 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____643 = FStar_Options.hide_uvar_nums ()  in
    if uu____643
    then "?"
    else
      (let uu____645 =
         let uu____646 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____646 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____645)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____652 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____653 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____652 uu____653
  
let (univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string)
  =
  fun u  ->
    let uu____659 = FStar_Options.hide_uvar_nums ()  in
    if uu____659
    then "?"
    else
      (let uu____661 =
         let uu____662 =
           let uu____663 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____663 FStar_Util.string_of_int  in
         let uu____664 =
           let uu____665 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____665  in
         Prims.strcat uu____662 uu____664  in
       Prims.strcat "?" uu____661)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____686 = FStar_Syntax_Subst.compress_univ u  in
      match uu____686 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____696 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____704 =
      let uu____705 = FStar_Options.ugly ()  in Prims.op_Negation uu____705
       in
    if uu____704
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____709 = FStar_Syntax_Subst.compress_univ u  in
       match uu____709 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____721 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____721
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____723 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____723 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____737 = univ_to_string u2  in
                let uu____738 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____737 uu____738)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____742 =
             let uu____743 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____743 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____742
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____757 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____757 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____767 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____767 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___98_778  ->
    match uu___98_778 with
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
        let uu____780 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____780
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____783 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____783 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____794 =
          let uu____795 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____795  in
        let uu____796 =
          let uu____797 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____797 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____794 uu____796
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____816 =
          let uu____817 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____817  in
        let uu____818 =
          let uu____819 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____819 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____816 uu____818
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____829 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____829
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
    | uu____840 ->
        let uu____843 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____843 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____861 ->
        let uu____864 = quals_to_string quals  in Prims.strcat uu____864 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____984 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____984
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____986 = nm_to_string x  in Prims.strcat "Tm_name: " uu____986
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____988 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____988
    | FStar_Syntax_Syntax.Tm_uinst uu____989 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____996 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____997 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____998,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____999;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1014,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1015;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1030 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1047 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1060 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1067 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1082 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1105 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1132 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1145 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1162,m) ->
        let uu____1204 = FStar_ST.op_Bang m  in
        (match uu____1204 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1264 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1269,m) ->
        let uu____1275 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1275
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1276 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1278 =
      let uu____1279 = FStar_Options.ugly ()  in Prims.op_Negation uu____1279
       in
    if uu____1278
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1285 = FStar_Options.print_implicits ()  in
         if uu____1285 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1287 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1312,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1332 =
             let uu____1333 =
               let uu____1342 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1342  in
             uu____1333 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1332
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1397;_})
           ->
           let uu____1412 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1412
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1414;_})
           ->
           let uu____1429 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1429
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1447 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1477 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1495  ->
                                 match uu____1495 with
                                 | (t1,uu____1501) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1477
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1447 (FStar_String.concat "\\/")  in
           let uu____1506 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1506
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1518 = tag_of_term t  in
           let uu____1519 = sli m  in
           let uu____1520 = term_to_string t'  in
           let uu____1521 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1518 uu____1519
             uu____1520 uu____1521
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1534 = tag_of_term t  in
           let uu____1535 = term_to_string t'  in
           let uu____1536 = sli m0  in
           let uu____1537 = sli m1  in
           let uu____1538 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1534
             uu____1535 uu____1536 uu____1537 uu____1538
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1547 = FStar_Range.string_of_range r  in
           let uu____1548 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1547
             uu____1548
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1555 = lid_to_string l  in
           let uu____1556 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1557 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1555 uu____1556
             uu____1557
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1559) ->
           let uu____1564 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1564
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1566 = db_to_string x3  in
           let uu____1567 =
             let uu____1568 =
               let uu____1569 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1569 ")"  in
             Prims.strcat ":(" uu____1568  in
           Prims.strcat uu____1566 uu____1567
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1573) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1600 = FStar_Options.print_universes ()  in
           if uu____1600
           then
             let uu____1601 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1601
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1621 = binders_to_string " -> " bs  in
           let uu____1622 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1621 uu____1622
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1647 = binders_to_string " " bs  in
                let uu____1648 = term_to_string t2  in
                let uu____1649 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1653 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1653)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1647 uu____1648
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1649
            | uu____1656 ->
                let uu____1659 = binders_to_string " " bs  in
                let uu____1660 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1659 uu____1660)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1667 = bv_to_string xt  in
           let uu____1668 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1671 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1667 uu____1668 uu____1671
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1696 = term_to_string t  in
           let uu____1697 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1696 uu____1697
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1716 = lbs_to_string [] lbs  in
           let uu____1717 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1716 uu____1717
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1778 =
                   let uu____1779 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1779
                     (FStar_Util.dflt "default")
                    in
                 let uu____1784 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1778 uu____1784
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1800 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1800
              in
           let uu____1801 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1801 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1840 = term_to_string head1  in
           let uu____1841 =
             let uu____1842 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1878  ->
                       match uu____1878 with
                       | (p,wopt,e) ->
                           let uu____1894 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1895 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1897 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1897
                              in
                           let uu____1898 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1894
                             uu____1895 uu____1898))
                in
             FStar_Util.concat_l "\n\t|" uu____1842  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1840 uu____1841
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1905 = FStar_Options.print_universes ()  in
           if uu____1905
           then
             let uu____1906 = term_to_string t  in
             let uu____1907 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1906 uu____1907
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1910 =
      let uu____1911 = FStar_Options.ugly ()  in Prims.op_Negation uu____1911
       in
    if uu____1910
    then
      let e =
        let uu____1913 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1913  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1936 = fv_to_string l  in
           let uu____1937 =
             let uu____1938 =
               FStar_List.map
                 (fun uu____1949  ->
                    match uu____1949 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1938 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1936 uu____1937
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1961) ->
           let uu____1966 = FStar_Options.print_bound_var_types ()  in
           if uu____1966
           then
             let uu____1967 = bv_to_string x1  in
             let uu____1968 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1967 uu____1968
           else
             (let uu____1970 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1970)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1972 = FStar_Options.print_bound_var_types ()  in
           if uu____1972
           then
             let uu____1973 = bv_to_string x1  in
             let uu____1974 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1973 uu____1974
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1978 = FStar_Options.print_real_names ()  in
           if uu____1978
           then
             let uu____1979 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1979
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1991 = quals_to_string' quals  in
      let uu____1992 =
        let uu____1993 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2009 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2010 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2011 =
                    let uu____2012 = FStar_Options.print_universes ()  in
                    if uu____2012
                    then
                      let uu____2013 =
                        let uu____2014 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2014 ">"  in
                      Prims.strcat "<" uu____2013
                    else ""  in
                  let uu____2016 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2017 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2009
                    uu____2010 uu____2011 uu____2016 uu____2017))
           in
        FStar_Util.concat_l "\n and " uu____1993  in
      FStar_Util.format3 "%slet %s %s" uu____1991
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1992

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___99_2023  ->
    match uu___99_2023 with
    | [] -> ""
    | tms ->
        let uu____2029 =
          let uu____2030 =
            FStar_List.map
              (fun t  ->
                 let uu____2036 = term_to_string t  in paren uu____2036) tms
             in
          FStar_All.pipe_right uu____2030 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2029

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2040 = FStar_Options.print_effect_args ()  in
    if uu____2040
    then
      let uu____2041 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2041
    else
      (let uu____2043 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2044 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2043 uu____2044)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___100_2045  ->
    match uu___100_2045 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2046 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2049 = aqual_to_string aq  in Prims.strcat uu____2049 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____2052 =
        let uu____2053 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2053  in
      if uu____2052
      then
        let uu____2054 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2054 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2060 = b  in
         match uu____2060 with
         | (a,imp) ->
             let uu____2063 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2063
             then
               let uu____2064 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2064
             else
               (let uu____2066 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2068 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2068)
                   in
                if uu____2066
                then
                  let uu____2069 = nm_to_string a  in
                  imp_to_string uu____2069 imp
                else
                  (let uu____2071 =
                     let uu____2072 = nm_to_string a  in
                     let uu____2073 =
                       let uu____2074 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2074  in
                     Prims.strcat uu____2072 uu____2073  in
                   imp_to_string uu____2071 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2080 = FStar_Options.print_implicits ()  in
        if uu____2080 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2082 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2082 (FStar_String.concat sep)
      else
        (let uu____2090 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2090 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___101_2097  ->
    match uu___101_2097 with
    | (a,imp) ->
        let uu____2104 = term_to_string a  in imp_to_string uu____2104 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2107 = FStar_Options.print_implicits ()  in
      if uu____2107 then args else filter_imp args  in
    let uu____2111 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2111 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2124 = FStar_Options.ugly ()  in
      if uu____2124
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2129 =
      let uu____2130 = FStar_Options.ugly ()  in Prims.op_Negation uu____2130
       in
    if uu____2129
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2144 =
             let uu____2145 = FStar_Syntax_Subst.compress t  in
             uu____2145.FStar_Syntax_Syntax.n  in
           (match uu____2144 with
            | FStar_Syntax_Syntax.Tm_type uu____2148 when
                let uu____2149 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2149 -> term_to_string t
            | uu____2150 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2152 = univ_to_string u  in
                     let uu____2153 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2152 uu____2153
                 | uu____2154 ->
                     let uu____2157 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2157))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2168 =
             let uu____2169 = FStar_Syntax_Subst.compress t  in
             uu____2169.FStar_Syntax_Syntax.n  in
           (match uu____2168 with
            | FStar_Syntax_Syntax.Tm_type uu____2172 when
                let uu____2173 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2173 -> term_to_string t
            | uu____2174 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2176 = univ_to_string u  in
                     let uu____2177 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2176 uu____2177
                 | uu____2178 ->
                     let uu____2181 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2181))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2184 = FStar_Options.print_effect_args ()  in
             if uu____2184
             then
               let uu____2185 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2186 =
                 let uu____2187 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2187 (FStar_String.concat ", ")
                  in
               let uu____2194 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2195 =
                 let uu____2196 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2196 (FStar_String.concat ", ")
                  in
               let uu____2215 =
                 let uu____2216 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2216 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2185
                 uu____2186 uu____2194 uu____2195 uu____2215
             else
               (let uu____2226 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___102_2230  ->
                           match uu___102_2230 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2231 -> false)))
                    &&
                    (let uu____2233 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2233)
                   in
                if uu____2226
                then
                  let uu____2234 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2234
                else
                  (let uu____2236 =
                     ((let uu____2239 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2239) &&
                        (let uu____2241 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2241))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2236
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2243 =
                        (let uu____2246 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2246) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___103_2250  ->
                                   match uu___103_2250 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2251 -> false)))
                         in
                      if uu____2243
                      then
                        let uu____2252 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2252
                      else
                        (let uu____2254 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2255 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2254 uu____2255))))
              in
           let dec =
             let uu____2257 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___104_2267  ->
                       match uu___104_2267 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2273 =
                             let uu____2274 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2274
                              in
                           [uu____2273]
                       | uu____2275 -> []))
                in
             FStar_All.pipe_right uu____2257 (FStar_String.concat " ")  in
           FStar_Util.format2 "%s%s" basic dec)

and (cflags_to_string : FStar_Syntax_Syntax.cflags -> Prims.string) =
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
    | FStar_Syntax_Syntax.DECREASES uu____2279 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___105_2285  ->
    match uu___105_2285 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2298 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2328 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2346  ->
                              match uu____2346 with
                              | (t,uu____2352) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2328
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2298 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2358 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2358
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2361) ->
        let uu____2362 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2362
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2370 = sli m  in
        let uu____2371 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2370 uu____2371
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2379 = sli m  in
        let uu____2380 = sli m'  in
        let uu____2381 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2379
          uu____2380 uu____2381

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2392 = FStar_Options.ugly ()  in
      if uu____2392
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
      let uu____2406 = b  in
      match uu____2406 with
      | (a,imp) ->
          let n1 =
            let uu____2410 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2410
            then FStar_Util.JsonNull
            else
              (let uu____2412 =
                 let uu____2413 = nm_to_string a  in
                 imp_to_string uu____2413 imp  in
               FStar_Util.JsonStr uu____2412)
             in
          let t =
            let uu____2415 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2415  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2438 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2438
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2446 = FStar_Options.print_universes ()  in
    if uu____2446 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2453 =
      let uu____2454 = FStar_Options.ugly ()  in Prims.op_Negation uu____2454
       in
    if uu____2453
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2458 = s  in
       match uu____2458 with
       | (us,t) ->
           let uu____2465 =
             let uu____2466 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2466  in
           let uu____2467 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2465 uu____2467)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2473 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2474 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2475 =
      let uu____2476 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2476  in
    let uu____2477 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2478 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2473 uu____2474 uu____2475
      uu____2477 uu____2478
  
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
          let uu____2503 =
            let uu____2504 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2504  in
          if uu____2503
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2518 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2518 (FStar_String.concat ",\n\t")
                in
             let uu____2527 =
               let uu____2530 =
                 let uu____2533 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2534 =
                   let uu____2537 =
                     let uu____2538 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2538  in
                   let uu____2539 =
                     let uu____2542 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2543 =
                       let uu____2546 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2547 =
                         let uu____2550 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2551 =
                           let uu____2554 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2555 =
                             let uu____2558 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2559 =
                               let uu____2562 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2563 =
                                 let uu____2566 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2567 =
                                   let uu____2570 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2571 =
                                     let uu____2574 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2575 =
                                       let uu____2578 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2579 =
                                         let uu____2582 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2583 =
                                           let uu____2586 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2587 =
                                             let uu____2590 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2591 =
                                               let uu____2594 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2595 =
                                                 let uu____2598 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2599 =
                                                   let uu____2602 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2602]  in
                                                 uu____2598 :: uu____2599  in
                                               uu____2594 :: uu____2595  in
                                             uu____2590 :: uu____2591  in
                                           uu____2586 :: uu____2587  in
                                         uu____2582 :: uu____2583  in
                                       uu____2578 :: uu____2579  in
                                     uu____2574 :: uu____2575  in
                                   uu____2570 :: uu____2571  in
                                 uu____2566 :: uu____2567  in
                               uu____2562 :: uu____2563  in
                             uu____2558 :: uu____2559  in
                           uu____2554 :: uu____2555  in
                         uu____2550 :: uu____2551  in
                       uu____2546 :: uu____2547  in
                     uu____2542 :: uu____2543  in
                   uu____2537 :: uu____2539  in
                 uu____2533 :: uu____2534  in
               (if for_free then "_for_free " else "") :: uu____2530  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2527)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2619 =
      let uu____2620 = FStar_Options.ugly ()  in Prims.op_Negation uu____2620
       in
    if uu____2619
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2626 -> ""
    else
      (let basic =
         match x.FStar_Syntax_Syntax.sigel with
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
             "#light \"off\""
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
             (FStar_Pervasives_Native.None )) -> "#reset-options"
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
             (FStar_Pervasives_Native.Some s)) ->
             FStar_Util.format1 "#reset-options \"%s\"" s
         | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s)
             -> FStar_Util.format1 "#set-options \"%s\"" s
         | FStar_Syntax_Syntax.Sig_inductive_typ
             (lid,univs1,tps,k,uu____2637,uu____2638) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2650 = FStar_Options.print_universes ()  in
             if uu____2650
             then
               let uu____2651 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2651 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2656,uu____2657,uu____2658) ->
             let uu____2663 = FStar_Options.print_universes ()  in
             if uu____2663
             then
               let uu____2664 = univ_names_to_string univs1  in
               let uu____2665 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2664
                 lid.FStar_Ident.str uu____2665
             else
               (let uu____2667 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2667)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2671 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2672 =
               let uu____2673 = FStar_Options.print_universes ()  in
               if uu____2673
               then
                 let uu____2674 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2674
               else ""  in
             let uu____2676 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2671
               lid.FStar_Ident.str uu____2672 uu____2676
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2678,f) ->
             let uu____2680 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2680
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2682) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2688 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2688
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2690) ->
             let uu____2699 =
               let uu____2700 = FStar_List.map sigelt_to_string ses  in
               FStar_All.pipe_right uu____2700 (FStar_String.concat "\n")  in
             Prims.strcat "(* Sig_bundle *)" uu____2699
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
               | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None
                  ) -> failwith "impossible"
               | (FStar_Pervasives_Native.Some lift_wp,uu____2718) -> lift_wp
               | (uu____2725,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2733 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2733 with
              | (us,t) ->
                  let uu____2744 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2745 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2746 = univ_names_to_string us  in
                  let uu____2747 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2744 uu____2745 uu____2746 uu____2747)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2757 = FStar_Options.print_universes ()  in
             if uu____2757
             then
               let uu____2758 =
                 let uu____2763 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2763  in
               (match uu____2758 with
                | (univs2,t) ->
                    let uu____2766 =
                      let uu____2779 =
                        let uu____2780 = FStar_Syntax_Subst.compress t  in
                        uu____2780.FStar_Syntax_Syntax.n  in
                      match uu____2779 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2821 -> failwith "impossible"  in
                    (match uu____2766 with
                     | (tps1,c1) ->
                         let uu____2852 = sli l  in
                         let uu____2853 = univ_names_to_string univs2  in
                         let uu____2854 = binders_to_string " " tps1  in
                         let uu____2855 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2852 uu____2853 uu____2854 uu____2855))
             else
               (let uu____2857 = sli l  in
                let uu____2858 = binders_to_string " " tps  in
                let uu____2859 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2857 uu____2858
                  uu____2859)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2866 =
               let uu____2867 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2867  in
             let uu____2872 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2866 uu____2872
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2873 ->
           let uu____2876 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2876 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2887 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2887 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2893,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2895;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2897;
                       FStar_Syntax_Syntax.lbdef = uu____2898;
                       FStar_Syntax_Syntax.lbattrs = uu____2899;
                       FStar_Syntax_Syntax.lbpos = uu____2900;_}::[]),uu____2901)
        ->
        let uu____2928 = lbname_to_string lb  in
        let uu____2929 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2928 uu____2929
    | uu____2930 ->
        let uu____2931 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2931 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2947 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2948 =
      let uu____2949 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2949 (FStar_String.concat "\n")  in
    let uu____2954 =
      let uu____2955 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2955 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2947 uu____2948 uu____2954
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___106_2964  ->
    match uu___106_2964 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2967 = FStar_Util.string_of_int i  in
        let uu____2968 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2967 uu____2968
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2971 = bv_to_string x  in
        let uu____2972 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2971 uu____2972
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2979 = bv_to_string x  in
        let uu____2980 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2979 uu____2980
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2983 = FStar_Util.string_of_int i  in
        let uu____2984 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2983 uu____2984
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2987 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2987
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2993 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2993 (FStar_String.concat "; ")
  
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
          (let uu____3029 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____3029))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____3036 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____3036)));
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
           (let uu____3070 = f x  in
            FStar_Util.string_builder_append strb uu____3070);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____3077 = f x1  in
                 FStar_Util.string_builder_append strb uu____3077)) xs;
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
           (let uu____3115 = f x  in
            FStar_Util.string_builder_append strb uu____3115);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____3122 = f x1  in
                 FStar_Util.string_builder_append strb uu____3122)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3138 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3138
  