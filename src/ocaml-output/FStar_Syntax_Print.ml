open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___68_3  ->
    match uu___68_3 with
    | FStar_Syntax_Syntax.Delta_constant  -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____5 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_defined_at_level " uu____5
    | FStar_Syntax_Syntax.Delta_equational  -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____7 =
          let uu____8 = delta_depth_to_string d  in Prims.strcat uu____8 ")"
           in
        Prims.strcat "Delta_abstract (" uu____7
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____12 = FStar_Options.print_real_names ()  in
    if uu____12
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____23 =
      let uu____24 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____24  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____23
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____28 = FStar_Options.print_real_names ()  in
    if uu____28
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____33 =
      let uu____34 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____34  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____33
  
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
      | uu____168 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____177 -> failwith "get_lid"
  
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
  'Auu____232 'Auu____233 .
    ('Auu____232,'Auu____233) FStar_Util.either -> Prims.bool
  =
  fun uu___69_241  ->
    match uu___69_241 with
    | FStar_Util.Inl uu____246 -> false
    | FStar_Util.Inr uu____247 -> true
  
let filter_imp :
  'Auu____250 .
    ('Auu____250,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____250,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___70_304  ->
            match uu___70_304 with
            | (uu____311,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____312)) -> false
            | uu____315 -> true))
  
let rec (reconstruct_lex :
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____331 =
      let uu____332 = FStar_Syntax_Subst.compress e  in
      uu____332.FStar_Syntax_Syntax.n  in
    match uu____331 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____395 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____395
        then
          let uu____404 =
            let uu____411 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____411  in
          (match uu____404 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____429 =
                 let uu____434 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____434 :: xs  in
               FStar_Pervasives_Native.Some uu____429
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____458 ->
        let uu____459 = is_lex_top e  in
        if uu____459
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____503 = f hd1  in if uu____503 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____523 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____523
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____545 = get_lid e  in find_lid uu____545 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____553 = get_lid e  in find_lid uu____553 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____561 = get_lid t  in find_lid uu____561 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___71_567  ->
    match uu___71_567 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____573 = FStar_Options.hide_uvar_nums ()  in
    if uu____573
    then "?"
    else
      (let uu____575 =
         let uu____576 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____576 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____575)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____580 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____581 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____580 uu____581
  
let (univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string)
  =
  fun u  ->
    let uu____585 = FStar_Options.hide_uvar_nums ()  in
    if uu____585
    then "?"
    else
      (let uu____587 =
         let uu____588 =
           let uu____589 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____589 FStar_Util.string_of_int  in
         let uu____590 =
           let uu____591 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____591  in
         Prims.strcat uu____588 uu____590  in
       Prims.strcat "?" uu____587)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____608 = FStar_Syntax_Subst.compress_univ u  in
      match uu____608 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____618 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____624 =
      let uu____625 = FStar_Options.ugly ()  in Prims.op_Negation uu____625
       in
    if uu____624
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____629 = FStar_Syntax_Subst.compress_univ u  in
       match uu____629 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____641 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____641
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____643 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____643 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____657 = univ_to_string u2  in
                let uu____658 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____657 uu____658)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____662 =
             let uu____663 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____663 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____662
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____675 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____675 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____683 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____683 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___72_692  ->
    match uu___72_692 with
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
        let uu____694 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____694
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____697 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____697 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____708 =
          let uu____709 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____709  in
        let uu____710 =
          let uu____711 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____711 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____708 uu____710
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____730 =
          let uu____731 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____731  in
        let uu____732 =
          let uu____733 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____733 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____730 uu____732
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____743 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____743
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
    | uu____752 ->
        let uu____755 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____755 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____771 ->
        let uu____774 = quals_to_string quals  in Prims.strcat uu____774 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____844 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____844
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____846 = nm_to_string x  in Prims.strcat "Tm_name: " uu____846
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____848 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____848
    | FStar_Syntax_Syntax.Tm_uinst uu____849 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____856 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____857 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____858,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____859;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____874,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_dynamic ;
                     FStar_Syntax_Syntax.antiquotes = uu____875;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____890 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____907 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____920 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____927 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____942 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____965 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____992 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1005 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1022,m) ->
        let uu____1064 = FStar_ST.op_Bang m  in
        (match uu____1064 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1120 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1125,m) ->
        let uu____1131 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1131
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1132 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1134 =
      let uu____1135 = FStar_Options.ugly ()  in Prims.op_Negation uu____1135
       in
    if uu____1134
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1141 = FStar_Options.print_implicits ()  in
         if uu____1141 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1143 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1168,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1188 =
             let uu____1189 =
               let uu____1194 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1194  in
             uu____1189 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1188
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1237;_})
           ->
           let uu____1252 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1252
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1254;_})
           ->
           let uu____1269 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1269
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1287 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1317 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1335  ->
                                 match uu____1335 with
                                 | (t1,uu____1341) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1317
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1287 (FStar_String.concat "\\/")  in
           let uu____1346 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1346
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1358 = tag_of_term t  in
           let uu____1359 = sli m  in
           let uu____1360 = term_to_string t'  in
           let uu____1361 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1358 uu____1359
             uu____1360 uu____1361
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1374 = tag_of_term t  in
           let uu____1375 = term_to_string t'  in
           let uu____1376 = sli m0  in
           let uu____1377 = sli m1  in
           let uu____1378 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1374
             uu____1375 uu____1376 uu____1377 uu____1378
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1387 = FStar_Range.string_of_range r  in
           let uu____1388 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1387
             uu____1388
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1395 = lid_to_string l  in
           let uu____1396 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1397 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1395 uu____1396
             uu____1397
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1399) ->
           let uu____1404 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1404
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1406 = db_to_string x3  in
           let uu____1407 =
             let uu____1408 =
               let uu____1409 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1409 ")"  in
             Prims.strcat ":(" uu____1408  in
           Prims.strcat uu____1406 uu____1407
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1413) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1440 = FStar_Options.print_universes ()  in
           if uu____1440
           then
             let uu____1441 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1441
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1461 = binders_to_string " -> " bs  in
           let uu____1462 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1461 uu____1462
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1487 = binders_to_string " " bs  in
                let uu____1488 = term_to_string t2  in
                let uu____1489 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1493 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1493)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1487 uu____1488
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1489
            | uu____1496 ->
                let uu____1499 = binders_to_string " " bs  in
                let uu____1500 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1499 uu____1500)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1507 = bv_to_string xt  in
           let uu____1508 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1511 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1507 uu____1508 uu____1511
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1536 = term_to_string t  in
           let uu____1537 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1536 uu____1537
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1556 = lbs_to_string [] lbs  in
           let uu____1557 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1556 uu____1557
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1618 =
                   let uu____1619 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1619
                     (FStar_Util.dflt "default")
                    in
                 let uu____1624 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1618 uu____1624
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1640 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1640
              in
           let uu____1641 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1641 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1680 = term_to_string head1  in
           let uu____1681 =
             let uu____1682 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1718  ->
                       match uu____1718 with
                       | (p,wopt,e) ->
                           let uu____1734 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1735 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1737 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1737
                              in
                           let uu____1738 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1734
                             uu____1735 uu____1738))
                in
             FStar_Util.concat_l "\n\t|" uu____1682  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1680 uu____1681
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1745 = FStar_Options.print_universes ()  in
           if uu____1745
           then
             let uu____1746 = term_to_string t  in
             let uu____1747 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1746 uu____1747
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1750 =
      let uu____1751 = FStar_Options.ugly ()  in Prims.op_Negation uu____1751
       in
    if uu____1750
    then
      let e =
        let uu____1753 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1753  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1776 = fv_to_string l  in
           let uu____1777 =
             let uu____1778 =
               FStar_List.map
                 (fun uu____1789  ->
                    match uu____1789 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1778 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1776 uu____1777
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1801) ->
           let uu____1806 = FStar_Options.print_bound_var_types ()  in
           if uu____1806
           then
             let uu____1807 = bv_to_string x1  in
             let uu____1808 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1807 uu____1808
           else
             (let uu____1810 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1810)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1812 = FStar_Options.print_bound_var_types ()  in
           if uu____1812
           then
             let uu____1813 = bv_to_string x1  in
             let uu____1814 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1813 uu____1814
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1818 = FStar_Options.print_real_names ()  in
           if uu____1818
           then
             let uu____1819 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1819
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1831 = quals_to_string' quals  in
      let uu____1832 =
        let uu____1833 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1849 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1850 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1851 =
                    let uu____1852 = FStar_Options.print_universes ()  in
                    if uu____1852
                    then
                      let uu____1853 =
                        let uu____1854 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1854 ">"  in
                      Prims.strcat "<" uu____1853
                    else ""  in
                  let uu____1856 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1857 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1849
                    uu____1850 uu____1851 uu____1856 uu____1857))
           in
        FStar_Util.concat_l "\n and " uu____1833  in
      FStar_Util.format3 "%slet %s %s" uu____1831
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1832

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___73_1863  ->
    match uu___73_1863 with
    | [] -> ""
    | tms ->
        let uu____1869 =
          let uu____1870 =
            FStar_List.map
              (fun t  ->
                 let uu____1876 = term_to_string t  in paren uu____1876) tms
             in
          FStar_All.pipe_right uu____1870 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1869

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1880 = FStar_Options.print_effect_args ()  in
    if uu____1880
    then
      let uu____1881 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1881
    else
      (let uu____1883 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1884 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1883 uu____1884)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___74_1885  ->
    match uu___74_1885 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1886 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1889 = aqual_to_string aq  in Prims.strcat uu____1889 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____1892 =
        let uu____1893 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1893  in
      if uu____1892
      then
        let uu____1894 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1894 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1900 = b  in
         match uu____1900 with
         | (a,imp) ->
             let uu____1903 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1903
             then
               let uu____1904 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1904
             else
               (let uu____1906 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1908 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1908)
                   in
                if uu____1906
                then
                  let uu____1909 = nm_to_string a  in
                  imp_to_string uu____1909 imp
                else
                  (let uu____1911 =
                     let uu____1912 = nm_to_string a  in
                     let uu____1913 =
                       let uu____1914 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1914  in
                     Prims.strcat uu____1912 uu____1913  in
                   imp_to_string uu____1911 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1920 = FStar_Options.print_implicits ()  in
        if uu____1920 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1922 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1922 (FStar_String.concat sep)
      else
        (let uu____1930 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1930 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___75_1937  ->
    match uu___75_1937 with
    | (a,imp) ->
        let uu____1944 = term_to_string a  in imp_to_string uu____1944 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____1947 = FStar_Options.print_implicits ()  in
      if uu____1947 then args else filter_imp args  in
    let uu____1951 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1951 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____1964 = FStar_Options.ugly ()  in
      if uu____1964
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____1969 =
      let uu____1970 = FStar_Options.ugly ()  in Prims.op_Negation uu____1970
       in
    if uu____1969
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1984 =
             let uu____1985 = FStar_Syntax_Subst.compress t  in
             uu____1985.FStar_Syntax_Syntax.n  in
           (match uu____1984 with
            | FStar_Syntax_Syntax.Tm_type uu____1988 when
                let uu____1989 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1989 -> term_to_string t
            | uu____1990 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1992 = univ_to_string u  in
                     let uu____1993 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____1992 uu____1993
                 | uu____1994 ->
                     let uu____1997 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____1997))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2008 =
             let uu____2009 = FStar_Syntax_Subst.compress t  in
             uu____2009.FStar_Syntax_Syntax.n  in
           (match uu____2008 with
            | FStar_Syntax_Syntax.Tm_type uu____2012 when
                let uu____2013 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2013 -> term_to_string t
            | uu____2014 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2016 = univ_to_string u  in
                     let uu____2017 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2016 uu____2017
                 | uu____2018 ->
                     let uu____2021 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2021))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2024 = FStar_Options.print_effect_args ()  in
             if uu____2024
             then
               let uu____2025 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2026 =
                 let uu____2027 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2027 (FStar_String.concat ", ")
                  in
               let uu____2034 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2035 =
                 let uu____2036 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2036 (FStar_String.concat ", ")
                  in
               let uu____2055 =
                 let uu____2056 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2056 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2025
                 uu____2026 uu____2034 uu____2035 uu____2055
             else
               (let uu____2066 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___76_2070  ->
                           match uu___76_2070 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2071 -> false)))
                    &&
                    (let uu____2073 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2073)
                   in
                if uu____2066
                then
                  let uu____2074 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2074
                else
                  (let uu____2076 =
                     ((let uu____2079 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2079) &&
                        (let uu____2081 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2081))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2076
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2083 =
                        (let uu____2086 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2086) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___77_2090  ->
                                   match uu___77_2090 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2091 -> false)))
                         in
                      if uu____2083
                      then
                        let uu____2092 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2092
                      else
                        (let uu____2094 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2095 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2094 uu____2095))))
              in
           let dec =
             let uu____2097 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___78_2107  ->
                       match uu___78_2107 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2113 =
                             let uu____2114 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2114
                              in
                           [uu____2113]
                       | uu____2115 -> []))
                in
             FStar_All.pipe_right uu____2097 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2119 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___79_2125  ->
    match uu___79_2125 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2138 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2168 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2186  ->
                              match uu____2186 with
                              | (t,uu____2192) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2168
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2138 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2198 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2198
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2201) ->
        let uu____2202 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2202
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2210 = sli m  in
        let uu____2211 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2210 uu____2211
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2219 = sli m  in
        let uu____2220 = sli m'  in
        let uu____2221 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2219
          uu____2220 uu____2221

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2228 = FStar_Options.ugly ()  in
      if uu____2228
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
      let uu____2238 = b  in
      match uu____2238 with
      | (a,imp) ->
          let n1 =
            let uu____2242 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2242
            then FStar_Util.JsonNull
            else
              (let uu____2244 =
                 let uu____2245 = nm_to_string a  in
                 imp_to_string uu____2245 imp  in
               FStar_Util.JsonStr uu____2244)
             in
          let t =
            let uu____2247 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2247  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2266 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2266
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2272 = FStar_Options.print_universes ()  in
    if uu____2272 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2277 =
      let uu____2278 = FStar_Options.ugly ()  in Prims.op_Negation uu____2278
       in
    if uu____2277
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2282 = s  in
       match uu____2282 with
       | (us,t) ->
           let uu____2289 =
             let uu____2290 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2290  in
           let uu____2291 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2289 uu____2291)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2295 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2296 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2297 =
      let uu____2298 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2298  in
    let uu____2299 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2300 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2295 uu____2296 uu____2297
      uu____2299 uu____2300
  
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
          let uu____2317 =
            let uu____2318 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2318  in
          if uu____2317
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2330 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2330 (FStar_String.concat ",\n\t")
                in
             let uu____2339 =
               let uu____2342 =
                 let uu____2345 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2346 =
                   let uu____2349 =
                     let uu____2350 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2350  in
                   let uu____2351 =
                     let uu____2354 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2355 =
                       let uu____2358 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2359 =
                         let uu____2362 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2363 =
                           let uu____2366 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2367 =
                             let uu____2370 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2371 =
                               let uu____2374 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2375 =
                                 let uu____2378 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2379 =
                                   let uu____2382 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2383 =
                                     let uu____2386 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2387 =
                                       let uu____2390 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2391 =
                                         let uu____2394 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2395 =
                                           let uu____2398 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2399 =
                                             let uu____2402 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2403 =
                                               let uu____2406 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2407 =
                                                 let uu____2410 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2411 =
                                                   let uu____2414 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2414]  in
                                                 uu____2410 :: uu____2411  in
                                               uu____2406 :: uu____2407  in
                                             uu____2402 :: uu____2403  in
                                           uu____2398 :: uu____2399  in
                                         uu____2394 :: uu____2395  in
                                       uu____2390 :: uu____2391  in
                                     uu____2386 :: uu____2387  in
                                   uu____2382 :: uu____2383  in
                                 uu____2378 :: uu____2379  in
                               uu____2374 :: uu____2375  in
                             uu____2370 :: uu____2371  in
                           uu____2366 :: uu____2367  in
                         uu____2362 :: uu____2363  in
                       uu____2358 :: uu____2359  in
                     uu____2354 :: uu____2355  in
                   uu____2349 :: uu____2351  in
                 uu____2345 :: uu____2346  in
               (if for_free then "_for_free " else "") :: uu____2342  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2339)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2425 =
      let uu____2426 = FStar_Options.ugly ()  in Prims.op_Negation uu____2426
       in
    if uu____2425
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2432 -> ""
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
             (lid,univs1,tps,k,uu____2443,uu____2444) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2456 = FStar_Options.print_universes ()  in
             if uu____2456
             then
               let uu____2457 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2457 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2462,uu____2463,uu____2464) ->
             let uu____2469 = FStar_Options.print_universes ()  in
             if uu____2469
             then
               let uu____2470 = univ_names_to_string univs1  in
               let uu____2471 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2470
                 lid.FStar_Ident.str uu____2471
             else
               (let uu____2473 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2473)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2477 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2478 =
               let uu____2479 = FStar_Options.print_universes ()  in
               if uu____2479
               then
                 let uu____2480 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2480
               else ""  in
             let uu____2482 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2477
               lid.FStar_Ident.str uu____2478 uu____2482
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2484,f) ->
             let uu____2486 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2486
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2488) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2494 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2494
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2496) ->
             let uu____2505 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2505 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2523) -> lift_wp
               | (uu____2530,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2538 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2538 with
              | (us,t) ->
                  let uu____2549 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2550 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2551 = univ_names_to_string us  in
                  let uu____2552 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2549 uu____2550 uu____2551 uu____2552)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2562 = FStar_Options.print_universes ()  in
             if uu____2562
             then
               let uu____2563 =
                 let uu____2568 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2568  in
               (match uu____2563 with
                | (univs2,t) ->
                    let uu____2571 =
                      let uu____2584 =
                        let uu____2585 = FStar_Syntax_Subst.compress t  in
                        uu____2585.FStar_Syntax_Syntax.n  in
                      match uu____2584 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2626 -> failwith "impossible"  in
                    (match uu____2571 with
                     | (tps1,c1) ->
                         let uu____2657 = sli l  in
                         let uu____2658 = univ_names_to_string univs2  in
                         let uu____2659 = binders_to_string " " tps1  in
                         let uu____2660 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2657 uu____2658 uu____2659 uu____2660))
             else
               (let uu____2662 = sli l  in
                let uu____2663 = binders_to_string " " tps  in
                let uu____2664 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2662 uu____2663
                  uu____2664)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2671 =
               let uu____2672 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2672  in
             let uu____2677 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2671 uu____2677
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2678 ->
           let uu____2681 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2681 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2688 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2688 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2692,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2694;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2696;
                       FStar_Syntax_Syntax.lbdef = uu____2697;
                       FStar_Syntax_Syntax.lbattrs = uu____2698;
                       FStar_Syntax_Syntax.lbpos = uu____2699;_}::[]),uu____2700)
        ->
        let uu____2727 = lbname_to_string lb  in
        let uu____2728 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2727 uu____2728
    | uu____2729 ->
        let uu____2730 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2730 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2744 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2745 =
      let uu____2746 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2746 (FStar_String.concat "\n")  in
    let uu____2751 =
      let uu____2752 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2752 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2744 uu____2745 uu____2751
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___80_2759  ->
    match uu___80_2759 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2762 = FStar_Util.string_of_int i  in
        let uu____2763 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2762 uu____2763
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2766 = bv_to_string x  in
        let uu____2767 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2766 uu____2767
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2774 = bv_to_string x  in
        let uu____2775 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2774 uu____2775
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2778 = FStar_Util.string_of_int i  in
        let uu____2779 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2778 uu____2779
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2782 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2782
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2786 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2786 (FStar_String.concat "; ")
  
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
          (let uu____2820 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____2820))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____2827 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____2827)));
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
           (let uu____2856 = f x  in
            FStar_Util.string_builder_append strb uu____2856);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2863 = f x1  in
                 FStar_Util.string_builder_append strb uu____2863)) xs;
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
           (let uu____2896 = f x  in
            FStar_Util.string_builder_append strb uu____2896);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2903 = f x1  in
                 FStar_Util.string_builder_append strb uu____2903)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____2915 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____2915
  