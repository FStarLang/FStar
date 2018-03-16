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
    ('Auu____232,'Auu____233) FStar_Util.either -> Prims.bool
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
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____683 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____683 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___70_692  ->
    match uu___70_692 with
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
        let uu____712 =
          let uu____713 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____713 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____708 uu____712
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____732 =
          let uu____733 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____733  in
        let uu____736 =
          let uu____737 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____737 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____732 uu____736
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____747 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____747
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
    | uu____756 ->
        let uu____759 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____759 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____775 ->
        let uu____778 = quals_to_string quals  in Prims.strcat uu____778 " "
  
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
    | FStar_Syntax_Syntax.Tm_lazy uu____1104 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1106 =
      let uu____1107 = FStar_Options.ugly ()  in Prims.op_Negation uu____1107
       in
    if uu____1106
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1113 = FStar_Options.print_implicits ()  in
         if uu____1113 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1115 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1140,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1160 =
             let uu____1161 =
               let uu____1166 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1166  in
             uu____1161 i.FStar_Syntax_Syntax.kind i  in
           term_to_string uu____1160
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1225 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1255 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1273  ->
                                 match uu____1273 with
                                 | (t1,uu____1279) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1255
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1225 (FStar_String.concat "\\/")  in
           let uu____1284 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1284
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1296 = tag_of_term t  in
           let uu____1297 = sli m  in
           let uu____1298 = term_to_string t'  in
           let uu____1299 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1296 uu____1297
             uu____1298 uu____1299
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1312 = tag_of_term t  in
           let uu____1313 = term_to_string t'  in
           let uu____1314 = sli m0  in
           let uu____1315 = sli m1  in
           let uu____1316 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1312
             uu____1313 uu____1314 uu____1315 uu____1316
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1325 = FStar_Range.string_of_range r  in
           let uu____1326 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1325
             uu____1326
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1333 = lid_to_string l  in
           let uu____1334 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1335 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1333 uu____1334
             uu____1335
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1337) ->
           let uu____1342 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1342
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_quoted (s,qi)) ->
           let uu____1354 = term_to_string s  in
           let uu____1355 =
             FStar_Util.string_of_bool qi.FStar_Syntax_Syntax.qopen  in
           FStar_Util.format2 "(Meta_quoted \"%s\" {qopen=%s})" uu____1354
             uu____1355
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1357 = db_to_string x3  in
           let uu____1358 =
             let uu____1359 =
               let uu____1360 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1360 ")"  in
             Prims.strcat ":(" uu____1359  in
           Prims.strcat uu____1357 uu____1358
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1364) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1391 = FStar_Options.print_universes ()  in
           if uu____1391
           then
             let uu____1392 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1392
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1412 = binders_to_string " -> " bs  in
           let uu____1413 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1412 uu____1413
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1438 = binders_to_string " " bs  in
                let uu____1439 = term_to_string t2  in
                let uu____1440 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1444 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1444)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1438 uu____1439
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1440
            | uu____1447 ->
                let uu____1450 = binders_to_string " " bs  in
                let uu____1451 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1450 uu____1451)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1458 = bv_to_string xt  in
           let uu____1459 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1462 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1458 uu____1459 uu____1462
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1487 = term_to_string t  in
           let uu____1488 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1487 uu____1488
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1507 = lbs_to_string [] lbs  in
           let uu____1508 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1507 uu____1508
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1569 =
                   let uu____1570 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1570
                     (FStar_Util.dflt "default")
                    in
                 let uu____1575 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1569 uu____1575
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1591 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1591
              in
           let uu____1592 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1592 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1631 = term_to_string head1  in
           let uu____1632 =
             let uu____1633 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1669  ->
                       match uu____1669 with
                       | (p,wopt,e) ->
                           let uu____1685 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1686 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1688 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1688
                              in
                           let uu____1689 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1685
                             uu____1686 uu____1689))
                in
             FStar_Util.concat_l "\n\t|" uu____1633  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1631 uu____1632
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1696 = FStar_Options.print_universes ()  in
           if uu____1696
           then
             let uu____1697 = term_to_string t  in
             let uu____1698 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1697 uu____1698
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1701 =
      let uu____1702 = FStar_Options.ugly ()  in Prims.op_Negation uu____1702
       in
    if uu____1701
    then
      let e =
        let uu____1704 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1704  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1727 = fv_to_string l  in
           let uu____1728 =
             let uu____1729 =
               FStar_List.map
                 (fun uu____1740  ->
                    match uu____1740 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1729 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1727 uu____1728
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1752) ->
           let uu____1757 = FStar_Options.print_bound_var_types ()  in
           if uu____1757
           then
             let uu____1758 = bv_to_string x1  in
             let uu____1759 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1758 uu____1759
           else
             (let uu____1761 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1761)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1763 = FStar_Options.print_bound_var_types ()  in
           if uu____1763
           then
             let uu____1764 = bv_to_string x1  in
             let uu____1765 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1764 uu____1765
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1769 = FStar_Options.print_real_names ()  in
           if uu____1769
           then
             let uu____1770 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1770
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1782 = quals_to_string' quals  in
      let uu____1783 =
        let uu____1784 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1800 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1801 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1802 =
                    let uu____1803 = FStar_Options.print_universes ()  in
                    if uu____1803
                    then
                      let uu____1804 =
                        let uu____1805 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1805 ">"  in
                      Prims.strcat "<" uu____1804
                    else ""  in
                  let uu____1807 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1808 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1800
                    uu____1801 uu____1802 uu____1807 uu____1808))
           in
        FStar_Util.concat_l "\n and " uu____1784  in
      FStar_Util.format3 "%slet %s %s" uu____1782
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1783

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___71_1814  ->
    match uu___71_1814 with
    | [] -> ""
    | tms ->
        let uu____1820 =
          let uu____1821 =
            FStar_List.map
              (fun t  ->
                 let uu____1827 = term_to_string t  in paren uu____1827) tms
             in
          FStar_All.pipe_right uu____1821 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1820

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1831 = FStar_Options.print_effect_args ()  in
    if uu____1831
    then
      let uu____1832 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1832
    else
      (let uu____1834 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1835 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1834 uu____1835)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___72_1836  ->
    match uu___72_1836 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1837 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1840 = aqual_to_string aq  in Prims.strcat uu____1840 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____1843 =
        let uu____1844 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1844  in
      if uu____1843
      then
        let uu____1845 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1845 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1851 = b  in
         match uu____1851 with
         | (a,imp) ->
             let uu____1854 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1854
             then
               let uu____1855 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1855
             else
               (let uu____1857 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1859 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1859)
                   in
                if uu____1857
                then
                  let uu____1860 = nm_to_string a  in
                  imp_to_string uu____1860 imp
                else
                  (let uu____1862 =
                     let uu____1863 = nm_to_string a  in
                     let uu____1864 =
                       let uu____1865 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1865  in
                     Prims.strcat uu____1863 uu____1864  in
                   imp_to_string uu____1862 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1871 = FStar_Options.print_implicits ()  in
        if uu____1871 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1873 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1873 (FStar_String.concat sep)
      else
        (let uu____1881 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1881 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___73_1888  ->
    match uu___73_1888 with
    | (a,imp) ->
        let uu____1895 = term_to_string a  in imp_to_string uu____1895 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____1898 = FStar_Options.print_implicits ()  in
      if uu____1898 then args else filter_imp args  in
    let uu____1902 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1902 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____1915 = FStar_Options.ugly ()  in
      if uu____1915
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____1920 =
      let uu____1921 = FStar_Options.ugly ()  in Prims.op_Negation uu____1921
       in
    if uu____1920
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1935 =
             let uu____1936 = FStar_Syntax_Subst.compress t  in
             uu____1936.FStar_Syntax_Syntax.n  in
           (match uu____1935 with
            | FStar_Syntax_Syntax.Tm_type uu____1939 when
                let uu____1940 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1940 -> term_to_string t
            | uu____1941 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1943 = univ_to_string u  in
                     let uu____1944 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____1943 uu____1944
                 | uu____1945 ->
                     let uu____1948 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____1948))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1959 =
             let uu____1960 = FStar_Syntax_Subst.compress t  in
             uu____1960.FStar_Syntax_Syntax.n  in
           (match uu____1959 with
            | FStar_Syntax_Syntax.Tm_type uu____1963 when
                let uu____1964 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1964 -> term_to_string t
            | uu____1965 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1967 = univ_to_string u  in
                     let uu____1968 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____1967 uu____1968
                 | uu____1969 ->
                     let uu____1972 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____1972))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1975 = FStar_Options.print_effect_args ()  in
             if uu____1975
             then
               let uu____1976 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____1977 =
                 let uu____1978 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____1978 (FStar_String.concat ", ")
                  in
               let uu____1985 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____1986 =
                 let uu____1987 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____1987 (FStar_String.concat ", ")
                  in
               let uu____2006 =
                 let uu____2007 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2007 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1976
                 uu____1977 uu____1985 uu____1986 uu____2006
             else
               (let uu____2017 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___74_2021  ->
                           match uu___74_2021 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2022 -> false)))
                    &&
                    (let uu____2024 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2024)
                   in
                if uu____2017
                then
                  let uu____2025 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2025
                else
                  (let uu____2027 =
                     ((let uu____2030 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2030) &&
                        (let uu____2032 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2032))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2027
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2034 =
                        (let uu____2037 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2037) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___75_2041  ->
                                   match uu___75_2041 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2042 -> false)))
                         in
                      if uu____2034
                      then
                        let uu____2043 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2043
                      else
                        (let uu____2045 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2046 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2045 uu____2046))))
              in
           let dec =
             let uu____2048 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___76_2058  ->
                       match uu___76_2058 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2064 =
                             let uu____2065 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2065
                              in
                           [uu____2064]
                       | uu____2066 -> []))
                in
             FStar_All.pipe_right uu____2048 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2070 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___77_2076  ->
    match uu___77_2076 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2089 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2119 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2137  ->
                              match uu____2137 with
                              | (t,uu____2143) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2119
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2089 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2149 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2149
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2152) ->
        let uu____2153 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2153
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2161 = sli m  in
        let uu____2162 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2161 uu____2162
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2170 = sli m  in
        let uu____2171 = sli m'  in
        let uu____2172 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2170
          uu____2171 uu____2172
    | FStar_Syntax_Syntax.Meta_quoted (qt,qi) ->
        let uu____2179 =
          let uu____2180 = term_to_string qt  in Prims.strcat uu____2180 ")"
           in
        Prims.strcat "`(" uu____2179

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2187 = FStar_Options.ugly ()  in
      if uu____2187
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
      let uu____2197 = b  in
      match uu____2197 with
      | (a,imp) ->
          let n1 =
            let uu____2201 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2201
            then FStar_Util.JsonNull
            else
              (let uu____2203 =
                 let uu____2204 = nm_to_string a  in
                 imp_to_string uu____2204 imp  in
               FStar_Util.JsonStr uu____2203)
             in
          let t =
            let uu____2206 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2206  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2225 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2225
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2231 = FStar_Options.print_universes ()  in
    if uu____2231 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2236 =
      let uu____2237 = FStar_Options.ugly ()  in Prims.op_Negation uu____2237
       in
    if uu____2236
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2241 = s  in
       match uu____2241 with
       | (us,t) ->
           let uu____2248 =
             let uu____2249 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2249  in
           let uu____2250 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2248 uu____2250)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2254 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2255 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2256 =
      let uu____2257 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2257  in
    let uu____2258 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2259 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2254 uu____2255 uu____2256
      uu____2258 uu____2259
  
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
          let uu____2276 =
            let uu____2277 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2277  in
          if uu____2276
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2289 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2289 (FStar_String.concat ",\n\t")
                in
             let uu____2298 =
               let uu____2301 =
                 let uu____2304 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2305 =
                   let uu____2308 =
                     let uu____2309 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2309  in
                   let uu____2310 =
                     let uu____2313 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2314 =
                       let uu____2317 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2318 =
                         let uu____2321 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2322 =
                           let uu____2325 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2326 =
                             let uu____2329 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2330 =
                               let uu____2333 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2334 =
                                 let uu____2337 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2338 =
                                   let uu____2341 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2342 =
                                     let uu____2345 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2346 =
                                       let uu____2349 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2350 =
                                         let uu____2353 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2354 =
                                           let uu____2357 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2358 =
                                             let uu____2361 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2362 =
                                               let uu____2365 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2366 =
                                                 let uu____2369 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2370 =
                                                   let uu____2373 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2373]  in
                                                 uu____2369 :: uu____2370  in
                                               uu____2365 :: uu____2366  in
                                             uu____2361 :: uu____2362  in
                                           uu____2357 :: uu____2358  in
                                         uu____2353 :: uu____2354  in
                                       uu____2349 :: uu____2350  in
                                     uu____2345 :: uu____2346  in
                                   uu____2341 :: uu____2342  in
                                 uu____2337 :: uu____2338  in
                               uu____2333 :: uu____2334  in
                             uu____2329 :: uu____2330  in
                           uu____2325 :: uu____2326  in
                         uu____2321 :: uu____2322  in
                       uu____2317 :: uu____2318  in
                     uu____2313 :: uu____2314  in
                   uu____2308 :: uu____2310  in
                 uu____2304 :: uu____2305  in
               (if for_free then "_for_free " else "") :: uu____2301  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2298)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2384 =
      let uu____2385 = FStar_Options.ugly ()  in Prims.op_Negation uu____2385
       in
    if uu____2384
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2391 -> ""
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
             (lid,univs1,tps,k,uu____2402,uu____2403) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2415 = FStar_Options.print_universes ()  in
             if uu____2415
             then
               let uu____2416 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2416 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2421,uu____2422,uu____2423) ->
             let uu____2428 = FStar_Options.print_universes ()  in
             if uu____2428
             then
               let uu____2429 = univ_names_to_string univs1  in
               let uu____2430 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2429
                 lid.FStar_Ident.str uu____2430
             else
               (let uu____2432 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2432)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2436 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2437 =
               let uu____2438 = FStar_Options.print_universes ()  in
               if uu____2438
               then
                 let uu____2439 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2439
               else ""  in
             let uu____2441 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2436
               lid.FStar_Ident.str uu____2437 uu____2441
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2443,f) ->
             let uu____2445 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2445
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2447) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2453 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2453
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2455) ->
             let uu____2464 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2464 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2482) -> lift_wp
               | (uu____2489,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2497 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2497 with
              | (us,t) ->
                  let uu____2508 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2509 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2510 = univ_names_to_string us  in
                  let uu____2511 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2508 uu____2509 uu____2510 uu____2511)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2521 = FStar_Options.print_universes ()  in
             if uu____2521
             then
               let uu____2522 =
                 let uu____2527 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2527  in
               (match uu____2522 with
                | (univs2,t) ->
                    let uu____2530 =
                      let uu____2543 =
                        let uu____2544 = FStar_Syntax_Subst.compress t  in
                        uu____2544.FStar_Syntax_Syntax.n  in
                      match uu____2543 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2585 -> failwith "impossible"  in
                    (match uu____2530 with
                     | (tps1,c1) ->
                         let uu____2616 = sli l  in
                         let uu____2617 = univ_names_to_string univs2  in
                         let uu____2618 = binders_to_string " " tps1  in
                         let uu____2619 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2616 uu____2617 uu____2618 uu____2619))
             else
               (let uu____2621 = sli l  in
                let uu____2622 = binders_to_string " " tps  in
                let uu____2623 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2621 uu____2622
                  uu____2623)
         | FStar_Syntax_Syntax.Sig_splice t ->
             let uu____2625 = term_to_string t  in
             FStar_Util.format1 "splice (%s)" uu____2625
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2626 ->
           let uu____2629 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2629 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2636 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2636 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2640,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2642;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2644;
                       FStar_Syntax_Syntax.lbdef = uu____2645;
                       FStar_Syntax_Syntax.lbattrs = uu____2646;
                       FStar_Syntax_Syntax.lbpos = uu____2647;_}::[]),uu____2648)
        ->
        let uu____2675 = lbname_to_string lb  in
        let uu____2676 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2675 uu____2676
    | uu____2677 ->
        let uu____2678 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2678 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2692 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2693 =
      let uu____2694 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2694 (FStar_String.concat "\n")  in
    let uu____2699 =
      let uu____2700 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2700 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2692 uu____2693 uu____2699
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___78_2707  ->
    match uu___78_2707 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2710 = FStar_Util.string_of_int i  in
        let uu____2711 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2710 uu____2711
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2714 = bv_to_string x  in
        let uu____2715 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2714 uu____2715
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2722 = bv_to_string x  in
        let uu____2723 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2722 uu____2723
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2726 = FStar_Util.string_of_int i  in
        let uu____2727 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2726 uu____2727
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2730 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2730
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2734 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2734 (FStar_String.concat "; ")
  
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
           (let uu____2802 = f x  in
            FStar_Util.string_builder_append strb uu____2802);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2809 = f x1  in
                 FStar_Util.string_builder_append strb uu____2809)) xs;
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
           (let uu____2842 = f x  in
            FStar_Util.string_builder_append strb uu____2842);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2849 = f x1  in
                 FStar_Util.string_builder_append strb uu____2849)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____2861 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____2861
  