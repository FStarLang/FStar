open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___64_3  ->
    match uu___64_3 with
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
  fun uu___65_241  ->
    match uu___65_241 with
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
         (fun uu___66_304  ->
            match uu___66_304 with
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
  fun uu___67_567  ->
    match uu___67_567 with
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
  fun uu___68_696  ->
    match uu___68_696 with
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
  
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____841 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____841
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____843 = nm_to_string x  in Prims.strcat "Tm_name: " uu____843
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____845 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____845
    | FStar_Syntax_Syntax.Tm_uinst uu____846 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____853 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____854 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____855 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____872 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____885 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____892 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____907 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____930 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____957 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____970 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____987,m) ->
        let uu____1029 = FStar_ST.op_Bang m  in
        (match uu____1029 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1137 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1142,m) ->
        let uu____1148 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1148
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1150 =
      let uu____1151 = FStar_Options.ugly ()  in Prims.op_Negation uu____1151
       in
    if uu____1150
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1157 = FStar_Options.print_implicits ()  in
         if uu____1157 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1159 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1184,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1220 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1250 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1268  ->
                                 match uu____1268 with
                                 | (t1,uu____1274) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1250
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1220 (FStar_String.concat "\\/")  in
           let uu____1279 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1279
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1291 = tag_of_term t  in
           let uu____1292 = sli m  in
           let uu____1293 = term_to_string t'  in
           let uu____1294 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1291 uu____1292
             uu____1293 uu____1294
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1307 = tag_of_term t  in
           let uu____1308 = term_to_string t'  in
           let uu____1309 = sli m0  in
           let uu____1310 = sli m1  in
           let uu____1311 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1307
             uu____1308 uu____1309 uu____1310 uu____1311
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1313,s,uu____1315)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1332 = FStar_Range.string_of_range r  in
           let uu____1333 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1332
             uu____1333
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1340 = lid_to_string l  in
           let uu____1341 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1342 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1340 uu____1341
             uu____1342
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1344) ->
           let uu____1349 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1349
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1351 = db_to_string x3  in
           let uu____1352 =
             let uu____1353 =
               let uu____1354 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1354 ")"  in
             Prims.strcat ":(" uu____1353  in
           Prims.strcat uu____1351 uu____1352
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1358) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1385 = FStar_Options.print_universes ()  in
           if uu____1385
           then
             let uu____1386 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1386
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1406 = binders_to_string " -> " bs  in
           let uu____1407 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1406 uu____1407
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1432 = binders_to_string " " bs  in
                let uu____1433 = term_to_string t2  in
                let uu____1434 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1438 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1438)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1432 uu____1433
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1434
            | uu____1441 ->
                let uu____1444 = binders_to_string " " bs  in
                let uu____1445 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1444 uu____1445)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1452 = bv_to_string xt  in
           let uu____1453 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1456 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1452 uu____1453 uu____1456
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1481 = term_to_string t  in
           let uu____1482 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1481 uu____1482
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1501 = lbs_to_string [] lbs  in
           let uu____1502 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1501 uu____1502
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1563 =
                   let uu____1564 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1564
                     (FStar_Util.dflt "default")
                    in
                 let uu____1569 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1563 uu____1569
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1585 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1585
              in
           let uu____1586 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1586 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1625 = term_to_string head1  in
           let uu____1626 =
             let uu____1627 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1663  ->
                       match uu____1663 with
                       | (p,wopt,e) ->
                           let uu____1679 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1680 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1682 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1682
                              in
                           let uu____1683 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1679
                             uu____1680 uu____1683))
                in
             FStar_Util.concat_l "\n\t|" uu____1627  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1625 uu____1626
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1690 = FStar_Options.print_universes ()  in
           if uu____1690
           then
             let uu____1691 = term_to_string t  in
             let uu____1692 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1691 uu____1692
           else term_to_string t
       | uu____1694 -> tag_of_term x2)

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1696 =
      let uu____1697 = FStar_Options.ugly ()  in Prims.op_Negation uu____1697
       in
    if uu____1696
    then
      let e = FStar_Syntax_Resugar.resugar_pat x  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1719 = fv_to_string l  in
           let uu____1720 =
             let uu____1721 =
               FStar_List.map
                 (fun uu____1732  ->
                    match uu____1732 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1721 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1719 uu____1720
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1744) ->
           let uu____1749 = FStar_Options.print_bound_var_types ()  in
           if uu____1749
           then
             let uu____1750 = bv_to_string x1  in
             let uu____1751 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1750 uu____1751
           else
             (let uu____1753 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1753)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1755 = FStar_Options.print_bound_var_types ()  in
           if uu____1755
           then
             let uu____1756 = bv_to_string x1  in
             let uu____1757 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1756 uu____1757
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1761 = FStar_Options.print_real_names ()  in
           if uu____1761
           then
             let uu____1762 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1762
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1774 = quals_to_string' quals  in
      let uu____1775 =
        let uu____1776 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1791 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1792 =
                    let uu____1793 = FStar_Options.print_universes ()  in
                    if uu____1793
                    then
                      let uu____1794 =
                        let uu____1795 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1795 ">"  in
                      Prims.strcat "<" uu____1794
                    else ""  in
                  let uu____1797 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1798 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1791 uu____1792
                    uu____1797 uu____1798))
           in
        FStar_Util.concat_l "\n and " uu____1776  in
      FStar_Util.format3 "%slet %s %s" uu____1774
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1775

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1805 = FStar_Options.print_effect_args ()  in
    if uu____1805
    then
      let uu____1806 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1806
    else
      (let uu____1808 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1809 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1808 uu____1809)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___69_1810  ->
    match uu___69_1810 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1811 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1814 = aqual_to_string aq  in Prims.strcat uu____1814 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____1817 =
        let uu____1818 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1818  in
      if uu____1817
      then
        let uu____1819 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1819 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1825 = b  in
         match uu____1825 with
         | (a,imp) ->
             let uu____1828 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1828
             then
               let uu____1829 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1829
             else
               (let uu____1831 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1833 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1833)
                   in
                if uu____1831
                then
                  let uu____1834 = nm_to_string a  in
                  imp_to_string uu____1834 imp
                else
                  (let uu____1836 =
                     let uu____1837 = nm_to_string a  in
                     let uu____1838 =
                       let uu____1839 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1839  in
                     Prims.strcat uu____1837 uu____1838  in
                   imp_to_string uu____1836 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1845 = FStar_Options.print_implicits ()  in
        if uu____1845 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1847 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1847 (FStar_String.concat sep)
      else
        (let uu____1855 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1855 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___70_1862  ->
    match uu___70_1862 with
    | (a,imp) ->
        let uu____1869 = term_to_string a  in imp_to_string uu____1869 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____1872 = FStar_Options.print_implicits ()  in
      if uu____1872 then args else filter_imp args  in
    let uu____1876 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1876 (FStar_String.concat " ")

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____1888 =
      let uu____1889 = FStar_Options.ugly ()  in Prims.op_Negation uu____1889
       in
    if uu____1888
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1903 =
             let uu____1904 = FStar_Syntax_Subst.compress t  in
             uu____1904.FStar_Syntax_Syntax.n  in
           (match uu____1903 with
            | FStar_Syntax_Syntax.Tm_type uu____1907 when
                let uu____1908 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1908 -> term_to_string t
            | uu____1909 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1911 = univ_to_string u  in
                     let uu____1912 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____1911 uu____1912
                 | uu____1913 ->
                     let uu____1916 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____1916))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1927 =
             let uu____1928 = FStar_Syntax_Subst.compress t  in
             uu____1928.FStar_Syntax_Syntax.n  in
           (match uu____1927 with
            | FStar_Syntax_Syntax.Tm_type uu____1931 when
                let uu____1932 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1932 -> term_to_string t
            | uu____1933 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1935 = univ_to_string u  in
                     let uu____1936 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____1935 uu____1936
                 | uu____1937 ->
                     let uu____1940 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____1940))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1943 = FStar_Options.print_effect_args ()  in
             if uu____1943
             then
               let uu____1944 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____1945 =
                 let uu____1946 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____1946 (FStar_String.concat ", ")
                  in
               let uu____1953 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____1954 =
                 let uu____1955 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____1955 (FStar_String.concat ", ")
                  in
               let uu____1974 =
                 let uu____1975 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____1975 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1944
                 uu____1945 uu____1953 uu____1954 uu____1974
             else
               (let uu____1985 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___71_1989  ->
                           match uu___71_1989 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1990 -> false)))
                    &&
                    (let uu____1992 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____1992)
                   in
                if uu____1985
                then
                  let uu____1993 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____1993
                else
                  (let uu____1995 =
                     ((let uu____1998 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____1998) &&
                        (let uu____2000 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2000))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____1995
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2002 =
                        (let uu____2005 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2005) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___72_2009  ->
                                   match uu___72_2009 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2010 -> false)))
                         in
                      if uu____2002
                      then
                        let uu____2011 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2011
                      else
                        (let uu____2013 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2014 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2013 uu____2014))))
              in
           let dec =
             let uu____2016 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___73_2026  ->
                       match uu___73_2026 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2032 =
                             let uu____2033 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2033
                              in
                           [uu____2032]
                       | uu____2034 -> []))
                in
             FStar_All.pipe_right uu____2016 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2038 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___74_2044  ->
    match uu___74_2044 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2057 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2087 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2105  ->
                              match uu____2105 with
                              | (t,uu____2111) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2087
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2057 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2117 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2117
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2120) ->
        let uu____2121 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2121
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2129 = sli m  in
        let uu____2130 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2129 uu____2130
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2138 = sli m  in
        let uu____2139 = sli m'  in
        let uu____2140 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2138
          uu____2139 uu____2140
    | FStar_Syntax_Syntax.Meta_alien (uu____2141,s,t) ->
        let uu____2148 = term_to_string t  in
        FStar_Util.format2 "{Meta_alien (%s, %s)}" s uu____2148

let (binder_to_json : FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun b  ->
    let uu____2152 = b  in
    match uu____2152 with
    | (a,imp) ->
        let n1 =
          let uu____2156 = FStar_Syntax_Syntax.is_null_binder b  in
          if uu____2156
          then FStar_Util.JsonNull
          else
            (let uu____2158 =
               let uu____2159 = nm_to_string a  in
               imp_to_string uu____2159 imp  in
             FStar_Util.JsonStr uu____2158)
           in
        let t =
          let uu____2161 = term_to_string a.FStar_Syntax_Syntax.sort  in
          FStar_Util.JsonStr uu____2161  in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json : FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun bs  ->
    let uu____2177 = FStar_List.map binder_to_json bs  in
    FStar_Util.JsonList uu____2177
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2183 = FStar_Options.print_universes ()  in
    if uu____2183 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2188 =
      let uu____2189 = FStar_Options.ugly ()  in Prims.op_Negation uu____2189
       in
    if uu____2188
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2193 = s  in
       match uu____2193 with
       | (us,t) ->
           let uu____2200 =
             let uu____2201 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2201  in
           let uu____2202 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2200 uu____2202)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2206 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2207 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2208 =
      let uu____2209 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2209  in
    let uu____2210 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2211 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2206 uu____2207 uu____2208
      uu____2210 uu____2211
  
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
          let uu____2228 =
            let uu____2229 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2229  in
          if uu____2228
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2241 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2241 (FStar_String.concat ",\n\t")
                in
             let uu____2250 =
               let uu____2253 =
                 let uu____2256 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2257 =
                   let uu____2260 =
                     let uu____2261 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2261  in
                   let uu____2262 =
                     let uu____2265 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2266 =
                       let uu____2269 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2270 =
                         let uu____2273 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2274 =
                           let uu____2277 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2278 =
                             let uu____2281 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2282 =
                               let uu____2285 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2286 =
                                 let uu____2289 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2290 =
                                   let uu____2293 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2294 =
                                     let uu____2297 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2298 =
                                       let uu____2301 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2302 =
                                         let uu____2305 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2306 =
                                           let uu____2309 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2310 =
                                             let uu____2313 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2314 =
                                               let uu____2317 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2318 =
                                                 let uu____2321 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2322 =
                                                   let uu____2325 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2325]  in
                                                 uu____2321 :: uu____2322  in
                                               uu____2317 :: uu____2318  in
                                             uu____2313 :: uu____2314  in
                                           uu____2309 :: uu____2310  in
                                         uu____2305 :: uu____2306  in
                                       uu____2301 :: uu____2302  in
                                     uu____2297 :: uu____2298  in
                                   uu____2293 :: uu____2294  in
                                 uu____2289 :: uu____2290  in
                               uu____2285 :: uu____2286  in
                             uu____2281 :: uu____2282  in
                           uu____2277 :: uu____2278  in
                         uu____2273 :: uu____2274  in
                       uu____2269 :: uu____2270  in
                     uu____2265 :: uu____2266  in
                   uu____2260 :: uu____2262  in
                 uu____2256 :: uu____2257  in
               (if for_free then "_for_free " else "") :: uu____2253  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2250)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2336 =
      let uu____2337 = FStar_Options.ugly ()  in Prims.op_Negation uu____2337
       in
    if uu____2336
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2343 -> ""
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
             (lid,univs1,tps,k,uu____2354,uu____2355) ->
             let uu____2364 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2365 = binders_to_string " " tps  in
             let uu____2366 = term_to_string k  in
             FStar_Util.format4 "%stype %s %s : %s" uu____2364
               lid.FStar_Ident.str uu____2365 uu____2366
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2370,uu____2371,uu____2372) ->
             let uu____2377 = FStar_Options.print_universes ()  in
             if uu____2377
             then
               let uu____2378 = univ_names_to_string univs1  in
               let uu____2379 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2378
                 lid.FStar_Ident.str uu____2379
             else
               (let uu____2381 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2381)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2385 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
             (match uu____2385 with
              | (univs2,t1) ->
                  let uu____2392 =
                    quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
                  let uu____2393 =
                    let uu____2394 = FStar_Options.print_universes ()  in
                    if uu____2394
                    then
                      let uu____2395 = univ_names_to_string univs2  in
                      FStar_Util.format1 "<%s>" uu____2395
                    else ""  in
                  let uu____2397 = term_to_string t1  in
                  FStar_Util.format4 "%sval %s %s : %s" uu____2392
                    lid.FStar_Ident.str uu____2393 uu____2397)
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2399,f) ->
             let uu____2401 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2401
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2403) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2409 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2409
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2411) ->
             let uu____2420 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2420 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2438) -> lift_wp
               | (uu____2445,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2453 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2453 with
              | (us,t) ->
                  let uu____2464 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2465 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2466 = univ_names_to_string us  in
                  let uu____2467 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2464 uu____2465 uu____2466 uu____2467)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2477 = FStar_Options.print_universes ()  in
             if uu____2477
             then
               let uu____2478 =
                 let uu____2483 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2483  in
               (match uu____2478 with
                | (univs2,t) ->
                    let uu____2486 =
                      let uu____2499 =
                        let uu____2500 = FStar_Syntax_Subst.compress t  in
                        uu____2500.FStar_Syntax_Syntax.n  in
                      match uu____2499 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2541 -> failwith "impossible"  in
                    (match uu____2486 with
                     | (tps1,c1) ->
                         let uu____2572 = sli l  in
                         let uu____2573 = univ_names_to_string univs2  in
                         let uu____2574 = binders_to_string " " tps1  in
                         let uu____2575 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2572 uu____2573 uu____2574 uu____2575))
             else
               (let uu____2577 = sli l  in
                let uu____2578 = binders_to_string " " tps  in
                let uu____2579 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2577 uu____2578
                  uu____2579)
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2580 ->
           let attrs =
             FStar_All.pipe_right x.FStar_Syntax_Syntax.sigattrs
               (FStar_List.map term_to_string)
              in
           let uu____2590 =
             FStar_All.pipe_right attrs (FStar_String.concat " ")  in
           FStar_Util.format2 "[@%s]\n%s" uu____2590 basic)
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2599 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2599 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2603,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2605;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2607;
                       FStar_Syntax_Syntax.lbdef = uu____2608;_}::[]),uu____2609)
        ->
        let uu____2632 = lbname_to_string lb  in
        let uu____2633 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2632 uu____2633
    | uu____2634 ->
        let uu____2635 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2635 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2649 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2650 =
      let uu____2651 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2651 (FStar_String.concat "\n")  in
    FStar_Util.format2 "module %s\n%s\n" uu____2649 uu____2650
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___75_2658  ->
    match uu___75_2658 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2661 = FStar_Util.string_of_int i  in
        let uu____2662 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2661 uu____2662
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2665 = bv_to_string x  in
        let uu____2666 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2665 uu____2666
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2673 = bv_to_string x  in
        let uu____2674 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2673 uu____2674
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2677 = FStar_Util.string_of_int i  in
        let uu____2678 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2677 uu____2678
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2681 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2681
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2685 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2685 (FStar_String.concat "; ")
  
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
           (let uu____2753 = f x  in
            FStar_Util.string_builder_append strb uu____2753);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2760 = f x1  in
                 FStar_Util.string_builder_append strb uu____2760)) xs;
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
           (let uu____2793 = f x  in
            FStar_Util.string_builder_append strb uu____2793);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2800 = f x1  in
                 FStar_Util.string_builder_append strb uu____2800)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  