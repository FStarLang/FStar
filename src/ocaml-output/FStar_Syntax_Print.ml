open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___66_3  ->
    match uu___66_3 with
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
    ('Auu____233,'Auu____232) FStar_Util.either -> Prims.bool
  =
  fun uu___67_241  ->
    match uu___67_241 with
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
         (fun uu___68_304  ->
            match uu___68_304 with
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
  fun uu___69_567  ->
    match uu___69_567 with
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
  
let (univ_names_to_string : FStar_Ident.ident Prims.list -> Prims.string) =
  fun us  ->
    let uu____687 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____687 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___70_696  ->
    match uu___70_696 with
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
        let uu____698 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____698
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____701 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____701 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____712 =
          let uu____713 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____713  in
        let uu____716 =
          let uu____717 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____717 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____712 uu____716
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____736 =
          let uu____737 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____737  in
        let uu____740 =
          let uu____741 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____741 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____736 uu____740
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____751 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____751
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
    | uu____760 ->
        let uu____763 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____763 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____779 ->
        let uu____782 = quals_to_string quals  in Prims.strcat uu____782 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____848 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____848
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____850 = nm_to_string x  in Prims.strcat "Tm_name: " uu____850
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____852 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____852
    | FStar_Syntax_Syntax.Tm_uinst uu____853 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____860 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____861 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____862 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____879 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____892 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____899 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____914 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____937 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____964 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____977 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____994,m) ->
        let uu____1036 = FStar_ST.op_Bang m  in
        (match uu____1036 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1092 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1097,m) ->
        let uu____1103 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1103
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1105 =
      let uu____1106 = FStar_Options.ugly ()  in Prims.op_Negation uu____1106
       in
    if uu____1105
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1112 = FStar_Options.print_implicits ()  in
         if uu____1112 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1114 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1139,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1175 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1205 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1223  ->
                                 match uu____1223 with
                                 | (t1,uu____1229) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1205
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1175 (FStar_String.concat "\\/")  in
           let uu____1234 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1234
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1246 = tag_of_term t  in
           let uu____1247 = sli m  in
           let uu____1248 = term_to_string t'  in
           let uu____1249 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1246 uu____1247
             uu____1248 uu____1249
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1262 = tag_of_term t  in
           let uu____1263 = term_to_string t'  in
           let uu____1264 = sli m0  in
           let uu____1265 = sli m1  in
           let uu____1266 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1262
             uu____1263 uu____1264 uu____1265 uu____1266
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1268,s,uu____1270)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1287 = FStar_Range.string_of_range r  in
           let uu____1288 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1287
             uu____1288
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1295 = lid_to_string l  in
           let uu____1296 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1297 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1295 uu____1296
             uu____1297
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1299) ->
           let uu____1304 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1304
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1306 = db_to_string x3  in
           let uu____1307 =
             let uu____1308 =
               let uu____1309 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1309 ")"  in
             Prims.strcat ":(" uu____1308  in
           Prims.strcat uu____1306 uu____1307
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1313) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1340 = FStar_Options.print_universes ()  in
           if uu____1340
           then
             let uu____1341 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1341
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1361 = binders_to_string " -> " bs  in
           let uu____1362 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1361 uu____1362
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1387 = binders_to_string " " bs  in
                let uu____1388 = term_to_string t2  in
                let uu____1389 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1393 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1393)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1387 uu____1388
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1389
            | uu____1396 ->
                let uu____1399 = binders_to_string " " bs  in
                let uu____1400 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1399 uu____1400)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1407 = bv_to_string xt  in
           let uu____1408 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1411 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1407 uu____1408 uu____1411
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1436 = term_to_string t  in
           let uu____1437 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1436 uu____1437
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1456 = lbs_to_string [] lbs  in
           let uu____1457 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1456 uu____1457
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1518 =
                   let uu____1519 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1519
                     (FStar_Util.dflt "default")
                    in
                 let uu____1524 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1518 uu____1524
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1540 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1540
              in
           let uu____1541 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1541 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1580 = term_to_string head1  in
           let uu____1581 =
             let uu____1582 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1618  ->
                       match uu____1618 with
                       | (p,wopt,e) ->
                           let uu____1634 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1635 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1637 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1637
                              in
                           let uu____1638 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1634
                             uu____1635 uu____1638))
                in
             FStar_Util.concat_l "\n\t|" uu____1582  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1580 uu____1581
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1645 = FStar_Options.print_universes ()  in
           if uu____1645
           then
             let uu____1646 = term_to_string t  in
             let uu____1647 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1646 uu____1647
           else term_to_string t
       | uu____1649 -> tag_of_term x2)

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1651 =
      let uu____1652 = FStar_Options.ugly ()  in Prims.op_Negation uu____1652
       in
    if uu____1651
    then
      let e = FStar_Syntax_Resugar.resugar_pat x  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1674 = fv_to_string l  in
           let uu____1675 =
             let uu____1676 =
               FStar_List.map
                 (fun uu____1687  ->
                    match uu____1687 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1676 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1674 uu____1675
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1699) ->
           let uu____1704 = FStar_Options.print_bound_var_types ()  in
           if uu____1704
           then
             let uu____1705 = bv_to_string x1  in
             let uu____1706 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1705 uu____1706
           else
             (let uu____1708 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1708)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1710 = FStar_Options.print_bound_var_types ()  in
           if uu____1710
           then
             let uu____1711 = bv_to_string x1  in
             let uu____1712 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1711 uu____1712
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1716 = FStar_Options.print_real_names ()  in
           if uu____1716
           then
             let uu____1717 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1717
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1729 = quals_to_string' quals  in
      let uu____1730 =
        let uu____1731 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1747 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1748 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1749 =
                    let uu____1750 = FStar_Options.print_universes ()  in
                    if uu____1750
                    then
                      let uu____1751 =
                        let uu____1752 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1752 ">"  in
                      Prims.strcat "<" uu____1751
                    else ""  in
                  let uu____1754 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1755 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1747
                    uu____1748 uu____1749 uu____1754 uu____1755))
           in
        FStar_Util.concat_l "\n and " uu____1731  in
      FStar_Util.format3 "%slet %s %s" uu____1729
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1730

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___71_1761  ->
    match uu___71_1761 with
    | [] -> ""
    | tms ->
        let uu____1767 =
          let uu____1768 =
            FStar_List.map
              (fun t  ->
                 let uu____1774 = term_to_string t  in paren uu____1774) tms
             in
          FStar_All.pipe_right uu____1768 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1767

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1778 = FStar_Options.print_effect_args ()  in
    if uu____1778
    then
      let uu____1779 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1779
    else
      (let uu____1781 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1782 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1781 uu____1782)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___72_1783  ->
    match uu___72_1783 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1784 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1787 = aqual_to_string aq  in Prims.strcat uu____1787 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____1790 =
        let uu____1791 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1791  in
      if uu____1790
      then
        let uu____1792 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1792 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1798 = b  in
         match uu____1798 with
         | (a,imp) ->
             let uu____1801 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1801
             then
               let uu____1802 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1802
             else
               (let uu____1804 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1806 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1806)
                   in
                if uu____1804
                then
                  let uu____1807 = nm_to_string a  in
                  imp_to_string uu____1807 imp
                else
                  (let uu____1809 =
                     let uu____1810 = nm_to_string a  in
                     let uu____1811 =
                       let uu____1812 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1812  in
                     Prims.strcat uu____1810 uu____1811  in
                   imp_to_string uu____1809 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1818 = FStar_Options.print_implicits ()  in
        if uu____1818 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1820 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1820 (FStar_String.concat sep)
      else
        (let uu____1828 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1828 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___73_1835  ->
    match uu___73_1835 with
    | (a,imp) ->
        let uu____1842 = term_to_string a  in imp_to_string uu____1842 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____1845 = FStar_Options.print_implicits ()  in
      if uu____1845 then args else filter_imp args  in
    let uu____1849 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1849 (FStar_String.concat " ")

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____1861 =
      let uu____1862 = FStar_Options.ugly ()  in Prims.op_Negation uu____1862
       in
    if uu____1861
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1876 =
             let uu____1877 = FStar_Syntax_Subst.compress t  in
             uu____1877.FStar_Syntax_Syntax.n  in
           (match uu____1876 with
            | FStar_Syntax_Syntax.Tm_type uu____1880 when
                let uu____1881 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1881 -> term_to_string t
            | uu____1882 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1884 = univ_to_string u  in
                     let uu____1885 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____1884 uu____1885
                 | uu____1886 ->
                     let uu____1889 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____1889))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1900 =
             let uu____1901 = FStar_Syntax_Subst.compress t  in
             uu____1901.FStar_Syntax_Syntax.n  in
           (match uu____1900 with
            | FStar_Syntax_Syntax.Tm_type uu____1904 when
                let uu____1905 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1905 -> term_to_string t
            | uu____1906 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1908 = univ_to_string u  in
                     let uu____1909 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____1908 uu____1909
                 | uu____1910 ->
                     let uu____1913 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____1913))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1916 = FStar_Options.print_effect_args ()  in
             if uu____1916
             then
               let uu____1917 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____1918 =
                 let uu____1919 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____1919 (FStar_String.concat ", ")
                  in
               let uu____1926 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____1927 =
                 let uu____1928 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____1928 (FStar_String.concat ", ")
                  in
               let uu____1947 =
                 let uu____1948 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____1948 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1917
                 uu____1918 uu____1926 uu____1927 uu____1947
             else
               (let uu____1958 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___74_1962  ->
                           match uu___74_1962 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1963 -> false)))
                    &&
                    (let uu____1965 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____1965)
                   in
                if uu____1958
                then
                  let uu____1966 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____1966
                else
                  (let uu____1968 =
                     ((let uu____1971 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____1971) &&
                        (let uu____1973 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____1973))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____1968
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1975 =
                        (let uu____1978 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____1978) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___75_1982  ->
                                   match uu___75_1982 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1983 -> false)))
                         in
                      if uu____1975
                      then
                        let uu____1984 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____1984
                      else
                        (let uu____1986 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____1987 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____1986 uu____1987))))
              in
           let dec =
             let uu____1989 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___76_1999  ->
                       match uu___76_1999 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2005 =
                             let uu____2006 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2006
                              in
                           [uu____2005]
                       | uu____2007 -> []))
                in
             FStar_All.pipe_right uu____1989 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2011 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___77_2017  ->
    match uu___77_2017 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2030 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2060 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2078  ->
                              match uu____2078 with
                              | (t,uu____2084) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2060
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2030 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2090 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2090
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2093) ->
        let uu____2094 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2094
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2102 = sli m  in
        let uu____2103 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2102 uu____2103
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2111 = sli m  in
        let uu____2112 = sli m'  in
        let uu____2113 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2111
          uu____2112 uu____2113
    | FStar_Syntax_Syntax.Meta_alien (uu____2114,s,t) ->
        let uu____2121 = term_to_string t  in
        FStar_Util.format2 "{Meta_alien (%s, %s)}" s uu____2121

let (binder_to_json : FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun b  ->
    let uu____2125 = b  in
    match uu____2125 with
    | (a,imp) ->
        let n1 =
          let uu____2129 = FStar_Syntax_Syntax.is_null_binder b  in
          if uu____2129
          then FStar_Util.JsonNull
          else
            (let uu____2131 =
               let uu____2132 = nm_to_string a  in
               imp_to_string uu____2132 imp  in
             FStar_Util.JsonStr uu____2131)
           in
        let t =
          let uu____2134 = term_to_string a.FStar_Syntax_Syntax.sort  in
          FStar_Util.JsonStr uu____2134  in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json : FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun bs  ->
    let uu____2150 = FStar_List.map binder_to_json bs  in
    FStar_Util.JsonList uu____2150
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2156 = FStar_Options.print_universes ()  in
    if uu____2156 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2161 =
      let uu____2162 = FStar_Options.ugly ()  in Prims.op_Negation uu____2162
       in
    if uu____2161
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2166 = s  in
       match uu____2166 with
       | (us,t) ->
           let uu____2173 =
             let uu____2174 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2174  in
           let uu____2175 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2173 uu____2175)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2179 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2180 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2181 =
      let uu____2182 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2182  in
    let uu____2183 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2184 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2179 uu____2180 uu____2181
      uu____2183 uu____2184
  
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
          let uu____2201 =
            let uu____2202 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2202  in
          if uu____2201
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2214 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2214 (FStar_String.concat ",\n\t")
                in
             let uu____2223 =
               let uu____2226 =
                 let uu____2229 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2230 =
                   let uu____2233 =
                     let uu____2234 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2234  in
                   let uu____2235 =
                     let uu____2238 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2239 =
                       let uu____2242 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2243 =
                         let uu____2246 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2247 =
                           let uu____2250 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2251 =
                             let uu____2254 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2255 =
                               let uu____2258 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2259 =
                                 let uu____2262 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2263 =
                                   let uu____2266 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2267 =
                                     let uu____2270 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2271 =
                                       let uu____2274 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2275 =
                                         let uu____2278 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2279 =
                                           let uu____2282 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2283 =
                                             let uu____2286 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2287 =
                                               let uu____2290 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2291 =
                                                 let uu____2294 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2295 =
                                                   let uu____2298 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2298]  in
                                                 uu____2294 :: uu____2295  in
                                               uu____2290 :: uu____2291  in
                                             uu____2286 :: uu____2287  in
                                           uu____2282 :: uu____2283  in
                                         uu____2278 :: uu____2279  in
                                       uu____2274 :: uu____2275  in
                                     uu____2270 :: uu____2271  in
                                   uu____2266 :: uu____2267  in
                                 uu____2262 :: uu____2263  in
                               uu____2258 :: uu____2259  in
                             uu____2254 :: uu____2255  in
                           uu____2250 :: uu____2251  in
                         uu____2246 :: uu____2247  in
                       uu____2242 :: uu____2243  in
                     uu____2238 :: uu____2239  in
                   uu____2233 :: uu____2235  in
                 uu____2229 :: uu____2230  in
               (if for_free then "_for_free " else "") :: uu____2226  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2223)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2309 =
      let uu____2310 = FStar_Options.ugly ()  in Prims.op_Negation uu____2310
       in
    if uu____2309
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2316 -> ""
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
             (lid,univs1,tps,k,uu____2327,uu____2328) ->
             let uu____2337 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2338 = binders_to_string " " tps  in
             let uu____2339 = term_to_string k  in
             FStar_Util.format4 "%stype %s %s : %s" uu____2337
               lid.FStar_Ident.str uu____2338 uu____2339
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2343,uu____2344,uu____2345) ->
             let uu____2350 = FStar_Options.print_universes ()  in
             if uu____2350
             then
               let uu____2351 = univ_names_to_string univs1  in
               let uu____2352 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2351
                 lid.FStar_Ident.str uu____2352
             else
               (let uu____2354 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2354)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2358 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
             (match uu____2358 with
              | (univs2,t1) ->
                  let uu____2365 =
                    quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
                  let uu____2366 =
                    let uu____2367 = FStar_Options.print_universes ()  in
                    if uu____2367
                    then
                      let uu____2368 = univ_names_to_string univs2  in
                      FStar_Util.format1 "<%s>" uu____2368
                    else ""  in
                  let uu____2370 = term_to_string t1  in
                  FStar_Util.format4 "%sval %s %s : %s" uu____2365
                    lid.FStar_Ident.str uu____2366 uu____2370)
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2372,f) ->
             let uu____2374 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2374
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2376) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2382 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2382
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2384) ->
             let uu____2393 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2393 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2411) -> lift_wp
               | (uu____2418,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2426 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2426 with
              | (us,t) ->
                  let uu____2437 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2438 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2439 = univ_names_to_string us  in
                  let uu____2440 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2437 uu____2438 uu____2439 uu____2440)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2450 = FStar_Options.print_universes ()  in
             if uu____2450
             then
               let uu____2451 =
                 let uu____2456 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2456  in
               (match uu____2451 with
                | (univs2,t) ->
                    let uu____2459 =
                      let uu____2472 =
                        let uu____2473 = FStar_Syntax_Subst.compress t  in
                        uu____2473.FStar_Syntax_Syntax.n  in
                      match uu____2472 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2514 -> failwith "impossible"  in
                    (match uu____2459 with
                     | (tps1,c1) ->
                         let uu____2545 = sli l  in
                         let uu____2546 = univ_names_to_string univs2  in
                         let uu____2547 = binders_to_string " " tps1  in
                         let uu____2548 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2545 uu____2546 uu____2547 uu____2548))
             else
               (let uu____2550 = sli l  in
                let uu____2551 = binders_to_string " " tps  in
                let uu____2552 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2550 uu____2551
                  uu____2552)
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2553 ->
           let uu____2556 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2556 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2563 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2563 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2567,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2569;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2571;
                       FStar_Syntax_Syntax.lbdef = uu____2572;
                       FStar_Syntax_Syntax.lbattrs = uu____2573;_}::[]),uu____2574)
        ->
        let uu____2601 = lbname_to_string lb  in
        let uu____2602 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2601 uu____2602
    | uu____2603 ->
        let uu____2604 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2604 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2618 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2619 =
      let uu____2620 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2620 (FStar_String.concat "\n")  in
    FStar_Util.format2 "module %s\n%s" uu____2618 uu____2619
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___78_2627  ->
    match uu___78_2627 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2630 = FStar_Util.string_of_int i  in
        let uu____2631 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2630 uu____2631
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2634 = bv_to_string x  in
        let uu____2635 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2634 uu____2635
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2642 = bv_to_string x  in
        let uu____2643 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2642 uu____2643
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2646 = FStar_Util.string_of_int i  in
        let uu____2647 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2646 uu____2647
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2650 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2650
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2654 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2654 (FStar_String.concat "; ")
  
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
          FStar_Util.string_builder_append strb
            (FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          FStar_Util.string_builder_append strb (FStar_Ident.text_of_lid lid)));
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
           (let uu____2722 = f x  in
            FStar_Util.string_builder_append strb uu____2722);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2729 = f x1  in
                 FStar_Util.string_builder_append strb uu____2729)) xs;
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
           (let uu____2762 = f x  in
            FStar_Util.string_builder_append strb uu____2762);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2769 = f x1  in
                 FStar_Util.string_builder_append strb uu____2769)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  