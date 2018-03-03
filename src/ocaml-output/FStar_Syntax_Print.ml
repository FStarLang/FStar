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
let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let e = FStar_Syntax_Resugar.resugar_term' env x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
  
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____856 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____856
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____858 = nm_to_string x  in Prims.strcat "Tm_name: " uu____858
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____860 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____860
    | FStar_Syntax_Syntax.Tm_uinst uu____861 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____868 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____869 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____870 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____887 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____900 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____907 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____922 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____945 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____972 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____985 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1002,m) ->
        let uu____1044 = FStar_ST.op_Bang m  in
        (match uu____1044 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1100 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1105,m) ->
        let uu____1111 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1111
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1112 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1114 =
      let uu____1115 = FStar_Options.ugly ()  in Prims.op_Negation uu____1115
       in
    if uu____1114
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1121 = FStar_Options.print_implicits ()  in
         if uu____1121 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1123 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1148,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1168 =
             let uu____1169 =
               let uu____1174 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1174  in
             uu____1169 i.FStar_Syntax_Syntax.kind i  in
           term_to_string uu____1168
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1233 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1263 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1281  ->
                                 match uu____1281 with
                                 | (t1,uu____1287) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1263
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1233 (FStar_String.concat "\\/")  in
           let uu____1292 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1292
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1304 = tag_of_term t  in
           let uu____1305 = sli m  in
           let uu____1306 = term_to_string t'  in
           let uu____1307 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1304 uu____1305
             uu____1306 uu____1307
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1320 = tag_of_term t  in
           let uu____1321 = term_to_string t'  in
           let uu____1322 = sli m0  in
           let uu____1323 = sli m1  in
           let uu____1324 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1320
             uu____1321 uu____1322 uu____1323 uu____1324
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1333 = FStar_Range.string_of_range r  in
           let uu____1334 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1333
             uu____1334
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1341 = lid_to_string l  in
           let uu____1342 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1343 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1341 uu____1342
             uu____1343
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1345) ->
           let uu____1350 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1350
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_quoted (s,uu____1353)) ->
           let uu____1362 = term_to_string s  in
           FStar_Util.format1 "(Meta_quoted \"%s\")" uu____1362
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1364 = db_to_string x3  in
           let uu____1365 =
             let uu____1366 =
               let uu____1367 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1367 ")"  in
             Prims.strcat ":(" uu____1366  in
           Prims.strcat uu____1364 uu____1365
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1371) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1398 = FStar_Options.print_universes ()  in
           if uu____1398
           then
             let uu____1399 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1399
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1419 = binders_to_string " -> " bs  in
           let uu____1420 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1419 uu____1420
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1445 = binders_to_string " " bs  in
                let uu____1446 = term_to_string t2  in
                let uu____1447 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1451 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1451)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1445 uu____1446
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1447
            | uu____1454 ->
                let uu____1457 = binders_to_string " " bs  in
                let uu____1458 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1457 uu____1458)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1465 = bv_to_string xt  in
           let uu____1466 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1469 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1465 uu____1466 uu____1469
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1494 = term_to_string t  in
           let uu____1495 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1494 uu____1495
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1514 = lbs_to_string [] lbs  in
           let uu____1515 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1514 uu____1515
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1576 =
                   let uu____1577 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1577
                     (FStar_Util.dflt "default")
                    in
                 let uu____1582 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1576 uu____1582
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1598 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1598
              in
           let uu____1599 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1599 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1638 = term_to_string head1  in
           let uu____1639 =
             let uu____1640 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1676  ->
                       match uu____1676 with
                       | (p,wopt,e) ->
                           let uu____1692 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1693 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1695 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1695
                              in
                           let uu____1696 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1692
                             uu____1693 uu____1696))
                in
             FStar_Util.concat_l "\n\t|" uu____1640  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1638 uu____1639
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1703 = FStar_Options.print_universes ()  in
           if uu____1703
           then
             let uu____1704 = term_to_string t  in
             let uu____1705 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1704 uu____1705
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1708 =
      let uu____1709 = FStar_Options.ugly ()  in Prims.op_Negation uu____1709
       in
    if uu____1708
    then
      let e =
        let uu____1711 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1711  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1734 = fv_to_string l  in
           let uu____1735 =
             let uu____1736 =
               FStar_List.map
                 (fun uu____1747  ->
                    match uu____1747 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1736 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1734 uu____1735
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1759) ->
           let uu____1764 = FStar_Options.print_bound_var_types ()  in
           if uu____1764
           then
             let uu____1765 = bv_to_string x1  in
             let uu____1766 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1765 uu____1766
           else
             (let uu____1768 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1768)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1770 = FStar_Options.print_bound_var_types ()  in
           if uu____1770
           then
             let uu____1771 = bv_to_string x1  in
             let uu____1772 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1771 uu____1772
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1776 = FStar_Options.print_real_names ()  in
           if uu____1776
           then
             let uu____1777 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1777
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1789 = quals_to_string' quals  in
      let uu____1790 =
        let uu____1791 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1807 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1808 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1809 =
                    let uu____1810 = FStar_Options.print_universes ()  in
                    if uu____1810
                    then
                      let uu____1811 =
                        let uu____1812 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1812 ">"  in
                      Prims.strcat "<" uu____1811
                    else ""  in
                  let uu____1814 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1815 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1807
                    uu____1808 uu____1809 uu____1814 uu____1815))
           in
        FStar_Util.concat_l "\n and " uu____1791  in
      FStar_Util.format3 "%slet %s %s" uu____1789
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1790

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___71_1821  ->
    match uu___71_1821 with
    | [] -> ""
    | tms ->
        let uu____1827 =
          let uu____1828 =
            FStar_List.map
              (fun t  ->
                 let uu____1834 = term_to_string t  in paren uu____1834) tms
             in
          FStar_All.pipe_right uu____1828 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1827

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1838 = FStar_Options.print_effect_args ()  in
    if uu____1838
    then
      let uu____1839 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1839
    else
      (let uu____1841 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1842 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1841 uu____1842)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___72_1843  ->
    match uu___72_1843 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1844 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1847 = aqual_to_string aq  in Prims.strcat uu____1847 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____1850 =
        let uu____1851 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1851  in
      if uu____1850
      then
        let uu____1852 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1852 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1858 = b  in
         match uu____1858 with
         | (a,imp) ->
             let uu____1861 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1861
             then
               let uu____1862 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1862
             else
               (let uu____1864 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1866 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1866)
                   in
                if uu____1864
                then
                  let uu____1867 = nm_to_string a  in
                  imp_to_string uu____1867 imp
                else
                  (let uu____1869 =
                     let uu____1870 = nm_to_string a  in
                     let uu____1871 =
                       let uu____1872 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1872  in
                     Prims.strcat uu____1870 uu____1871  in
                   imp_to_string uu____1869 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1878 = FStar_Options.print_implicits ()  in
        if uu____1878 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1880 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1880 (FStar_String.concat sep)
      else
        (let uu____1888 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1888 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___73_1895  ->
    match uu___73_1895 with
    | (a,imp) ->
        let uu____1902 = term_to_string a  in imp_to_string uu____1902 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____1905 = FStar_Options.print_implicits ()  in
      if uu____1905 then args else filter_imp args  in
    let uu____1909 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1909 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let e = FStar_Syntax_Resugar.resugar_comp' env c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____1925 =
      let uu____1926 = FStar_Options.ugly ()  in Prims.op_Negation uu____1926
       in
    if uu____1925
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1940 =
             let uu____1941 = FStar_Syntax_Subst.compress t  in
             uu____1941.FStar_Syntax_Syntax.n  in
           (match uu____1940 with
            | FStar_Syntax_Syntax.Tm_type uu____1944 when
                let uu____1945 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1945 -> term_to_string t
            | uu____1946 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1948 = univ_to_string u  in
                     let uu____1949 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____1948 uu____1949
                 | uu____1950 ->
                     let uu____1953 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____1953))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1964 =
             let uu____1965 = FStar_Syntax_Subst.compress t  in
             uu____1965.FStar_Syntax_Syntax.n  in
           (match uu____1964 with
            | FStar_Syntax_Syntax.Tm_type uu____1968 when
                let uu____1969 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1969 -> term_to_string t
            | uu____1970 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1972 = univ_to_string u  in
                     let uu____1973 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____1972 uu____1973
                 | uu____1974 ->
                     let uu____1977 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____1977))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1980 = FStar_Options.print_effect_args ()  in
             if uu____1980
             then
               let uu____1981 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____1982 =
                 let uu____1983 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____1983 (FStar_String.concat ", ")
                  in
               let uu____1990 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____1991 =
                 let uu____1992 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____1992 (FStar_String.concat ", ")
                  in
               let uu____2011 =
                 let uu____2012 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2012 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1981
                 uu____1982 uu____1990 uu____1991 uu____2011
             else
               (let uu____2022 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___74_2026  ->
                           match uu___74_2026 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2027 -> false)))
                    &&
                    (let uu____2029 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2029)
                   in
                if uu____2022
                then
                  let uu____2030 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2030
                else
                  (let uu____2032 =
                     ((let uu____2035 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2035) &&
                        (let uu____2037 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2037))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2032
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2039 =
                        (let uu____2042 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2042) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___75_2046  ->
                                   match uu___75_2046 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2047 -> false)))
                         in
                      if uu____2039
                      then
                        let uu____2048 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2048
                      else
                        (let uu____2050 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2051 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2050 uu____2051))))
              in
           let dec =
             let uu____2053 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___76_2063  ->
                       match uu___76_2063 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2069 =
                             let uu____2070 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2070
                              in
                           [uu____2069]
                       | uu____2071 -> []))
                in
             FStar_All.pipe_right uu____2053 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2075 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___77_2081  ->
    match uu___77_2081 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2094 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2124 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2142  ->
                              match uu____2142 with
                              | (t,uu____2148) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2124
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2094 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2154 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2154
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2157) ->
        let uu____2158 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2158
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2166 = sli m  in
        let uu____2167 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2166 uu____2167
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2175 = sli m  in
        let uu____2176 = sli m'  in
        let uu____2177 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2175
          uu____2176 uu____2177
    | FStar_Syntax_Syntax.Meta_quoted (qt,qi) ->
        let uu____2184 =
          let uu____2185 = term_to_string qt  in Prims.strcat uu____2185 ")"
           in
        Prims.strcat "`(" uu____2184

let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env  ->
    fun b  ->
      let uu____2192 = b  in
      match uu____2192 with
      | (a,imp) ->
          let n1 =
            let uu____2196 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2196
            then FStar_Util.JsonNull
            else
              (let uu____2198 =
                 let uu____2199 = nm_to_string a  in
                 imp_to_string uu____2199 imp  in
               FStar_Util.JsonStr uu____2198)
             in
          let t =
            let uu____2201 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2201  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2220 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2220
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2226 = FStar_Options.print_universes ()  in
    if uu____2226 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2231 =
      let uu____2232 = FStar_Options.ugly ()  in Prims.op_Negation uu____2232
       in
    if uu____2231
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2236 = s  in
       match uu____2236 with
       | (us,t) ->
           let uu____2243 =
             let uu____2244 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2244  in
           let uu____2245 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2243 uu____2245)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2249 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2250 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2251 =
      let uu____2252 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2252  in
    let uu____2253 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2254 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2249 uu____2250 uu____2251
      uu____2253 uu____2254
  
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
          let uu____2271 =
            let uu____2272 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2272  in
          if uu____2271
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2284 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2284 (FStar_String.concat ",\n\t")
                in
             let uu____2293 =
               let uu____2296 =
                 let uu____2299 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2300 =
                   let uu____2303 =
                     let uu____2304 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2304  in
                   let uu____2305 =
                     let uu____2308 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2309 =
                       let uu____2312 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2313 =
                         let uu____2316 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2317 =
                           let uu____2320 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2321 =
                             let uu____2324 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2325 =
                               let uu____2328 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2329 =
                                 let uu____2332 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2333 =
                                   let uu____2336 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2337 =
                                     let uu____2340 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2341 =
                                       let uu____2344 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2345 =
                                         let uu____2348 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2349 =
                                           let uu____2352 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2353 =
                                             let uu____2356 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2357 =
                                               let uu____2360 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2361 =
                                                 let uu____2364 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2365 =
                                                   let uu____2368 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2368]  in
                                                 uu____2364 :: uu____2365  in
                                               uu____2360 :: uu____2361  in
                                             uu____2356 :: uu____2357  in
                                           uu____2352 :: uu____2353  in
                                         uu____2348 :: uu____2349  in
                                       uu____2344 :: uu____2345  in
                                     uu____2340 :: uu____2341  in
                                   uu____2336 :: uu____2337  in
                                 uu____2332 :: uu____2333  in
                               uu____2328 :: uu____2329  in
                             uu____2324 :: uu____2325  in
                           uu____2320 :: uu____2321  in
                         uu____2316 :: uu____2317  in
                       uu____2312 :: uu____2313  in
                     uu____2308 :: uu____2309  in
                   uu____2303 :: uu____2305  in
                 uu____2299 :: uu____2300  in
               (if for_free then "_for_free " else "") :: uu____2296  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2293)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2379 =
      let uu____2380 = FStar_Options.ugly ()  in Prims.op_Negation uu____2380
       in
    if uu____2379
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2386 -> ""
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
             (lid,univs1,tps,k,uu____2397,uu____2398) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2410 = FStar_Options.print_universes ()  in
             if uu____2410
             then
               let uu____2411 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2411 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2416,uu____2417,uu____2418) ->
             let uu____2423 = FStar_Options.print_universes ()  in
             if uu____2423
             then
               let uu____2424 = univ_names_to_string univs1  in
               let uu____2425 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2424
                 lid.FStar_Ident.str uu____2425
             else
               (let uu____2427 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2427)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2431 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
             (match uu____2431 with
              | (univs2,t1) ->
                  let uu____2438 =
                    quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
                  let uu____2439 =
                    let uu____2440 = FStar_Options.print_universes ()  in
                    if uu____2440
                    then
                      let uu____2441 = univ_names_to_string univs2  in
                      FStar_Util.format1 "<%s>" uu____2441
                    else ""  in
                  let uu____2443 = term_to_string t1  in
                  FStar_Util.format4 "%sval %s %s : %s" uu____2438
                    lid.FStar_Ident.str uu____2439 uu____2443)
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2445,f) ->
             let uu____2447 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2447
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2449) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2455 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2455
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2457) ->
             let uu____2466 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2466 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2484) -> lift_wp
               | (uu____2491,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2499 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2499 with
              | (us,t) ->
                  let uu____2510 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2511 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2512 = univ_names_to_string us  in
                  let uu____2513 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2510 uu____2511 uu____2512 uu____2513)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2523 = FStar_Options.print_universes ()  in
             if uu____2523
             then
               let uu____2524 =
                 let uu____2529 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2529  in
               (match uu____2524 with
                | (univs2,t) ->
                    let uu____2532 =
                      let uu____2545 =
                        let uu____2546 = FStar_Syntax_Subst.compress t  in
                        uu____2546.FStar_Syntax_Syntax.n  in
                      match uu____2545 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2587 -> failwith "impossible"  in
                    (match uu____2532 with
                     | (tps1,c1) ->
                         let uu____2618 = sli l  in
                         let uu____2619 = univ_names_to_string univs2  in
                         let uu____2620 = binders_to_string " " tps1  in
                         let uu____2621 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2618 uu____2619 uu____2620 uu____2621))
             else
               (let uu____2623 = sli l  in
                let uu____2624 = binders_to_string " " tps  in
                let uu____2625 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2623 uu____2624
                  uu____2625)
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
                       FStar_Syntax_Syntax.lbattrs = uu____2646;_}::[]),uu____2647)
        ->
        let uu____2674 = lbname_to_string lb  in
        let uu____2675 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2674 uu____2675
    | uu____2676 ->
        let uu____2677 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2677 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2691 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2692 =
      let uu____2693 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2693 (FStar_String.concat "\n")  in
    let uu____2698 =
      let uu____2699 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2699 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2691 uu____2692 uu____2698
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___78_2706  ->
    match uu___78_2706 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2709 = FStar_Util.string_of_int i  in
        let uu____2710 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2709 uu____2710
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2713 = bv_to_string x  in
        let uu____2714 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2713 uu____2714
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2721 = bv_to_string x  in
        let uu____2722 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2721 uu____2722
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2725 = FStar_Util.string_of_int i  in
        let uu____2726 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2725 uu____2726
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2729 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2729
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2733 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2733 (FStar_String.concat "; ")
  
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
           (let uu____2801 = f x  in
            FStar_Util.string_builder_append strb uu____2801);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2808 = f x1  in
                 FStar_Util.string_builder_append strb uu____2808)) xs;
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
           (let uu____2841 = f x  in
            FStar_Util.string_builder_append strb uu____2841);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2848 = f x1  in
                 FStar_Util.string_builder_append strb uu____2848)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____2860 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____2860
  