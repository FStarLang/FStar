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
           (t,FStar_Syntax_Syntax.Meta_quoted (s,qi)) ->
           let uu____1362 = term_to_string s  in
           let uu____1363 =
             FStar_Util.string_of_bool qi.FStar_Syntax_Syntax.qopen  in
           FStar_Util.format2 "(Meta_quoted \"%s\" {qopen=%s})" uu____1362
             uu____1363
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1365 = db_to_string x3  in
           let uu____1366 =
             let uu____1367 =
               let uu____1368 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1368 ")"  in
             Prims.strcat ":(" uu____1367  in
           Prims.strcat uu____1365 uu____1366
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1372) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1399 = FStar_Options.print_universes ()  in
           if uu____1399
           then
             let uu____1400 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1400
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1420 = binders_to_string " -> " bs  in
           let uu____1421 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1420 uu____1421
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1446 = binders_to_string " " bs  in
                let uu____1447 = term_to_string t2  in
                let uu____1448 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1452 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1452)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1446 uu____1447
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1448
            | uu____1455 ->
                let uu____1458 = binders_to_string " " bs  in
                let uu____1459 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1458 uu____1459)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1466 = bv_to_string xt  in
           let uu____1467 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1470 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1466 uu____1467 uu____1470
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1495 = term_to_string t  in
           let uu____1496 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1495 uu____1496
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1515 = lbs_to_string [] lbs  in
           let uu____1516 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1515 uu____1516
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1577 =
                   let uu____1578 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1578
                     (FStar_Util.dflt "default")
                    in
                 let uu____1583 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1577 uu____1583
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1599 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1599
              in
           let uu____1600 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1600 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1639 = term_to_string head1  in
           let uu____1640 =
             let uu____1641 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1677  ->
                       match uu____1677 with
                       | (p,wopt,e) ->
                           let uu____1693 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1694 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1696 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1696
                              in
                           let uu____1697 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1693
                             uu____1694 uu____1697))
                in
             FStar_Util.concat_l "\n\t|" uu____1641  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1639 uu____1640
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1704 = FStar_Options.print_universes ()  in
           if uu____1704
           then
             let uu____1705 = term_to_string t  in
             let uu____1706 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1705 uu____1706
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1709 =
      let uu____1710 = FStar_Options.ugly ()  in Prims.op_Negation uu____1710
       in
    if uu____1709
    then
      let e =
        let uu____1712 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1712  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1735 = fv_to_string l  in
           let uu____1736 =
             let uu____1737 =
               FStar_List.map
                 (fun uu____1748  ->
                    match uu____1748 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1737 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1735 uu____1736
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1760) ->
           let uu____1765 = FStar_Options.print_bound_var_types ()  in
           if uu____1765
           then
             let uu____1766 = bv_to_string x1  in
             let uu____1767 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1766 uu____1767
           else
             (let uu____1769 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1769)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1771 = FStar_Options.print_bound_var_types ()  in
           if uu____1771
           then
             let uu____1772 = bv_to_string x1  in
             let uu____1773 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1772 uu____1773
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1777 = FStar_Options.print_real_names ()  in
           if uu____1777
           then
             let uu____1778 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1778
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1790 = quals_to_string' quals  in
      let uu____1791 =
        let uu____1792 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1808 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1809 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1810 =
                    let uu____1811 = FStar_Options.print_universes ()  in
                    if uu____1811
                    then
                      let uu____1812 =
                        let uu____1813 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1813 ">"  in
                      Prims.strcat "<" uu____1812
                    else ""  in
                  let uu____1815 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1816 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1808
                    uu____1809 uu____1810 uu____1815 uu____1816))
           in
        FStar_Util.concat_l "\n and " uu____1792  in
      FStar_Util.format3 "%slet %s %s" uu____1790
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1791

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___71_1822  ->
    match uu___71_1822 with
    | [] -> ""
    | tms ->
        let uu____1828 =
          let uu____1829 =
            FStar_List.map
              (fun t  ->
                 let uu____1835 = term_to_string t  in paren uu____1835) tms
             in
          FStar_All.pipe_right uu____1829 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1828

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1839 = FStar_Options.print_effect_args ()  in
    if uu____1839
    then
      let uu____1840 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1840
    else
      (let uu____1842 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1843 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1842 uu____1843)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___72_1844  ->
    match uu___72_1844 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1845 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1848 = aqual_to_string aq  in Prims.strcat uu____1848 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____1851 =
        let uu____1852 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1852  in
      if uu____1851
      then
        let uu____1853 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1853 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1859 = b  in
         match uu____1859 with
         | (a,imp) ->
             let uu____1862 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1862
             then
               let uu____1863 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1863
             else
               (let uu____1865 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1867 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1867)
                   in
                if uu____1865
                then
                  let uu____1868 = nm_to_string a  in
                  imp_to_string uu____1868 imp
                else
                  (let uu____1870 =
                     let uu____1871 = nm_to_string a  in
                     let uu____1872 =
                       let uu____1873 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1873  in
                     Prims.strcat uu____1871 uu____1872  in
                   imp_to_string uu____1870 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1879 = FStar_Options.print_implicits ()  in
        if uu____1879 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1881 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1881 (FStar_String.concat sep)
      else
        (let uu____1889 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1889 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___73_1896  ->
    match uu___73_1896 with
    | (a,imp) ->
        let uu____1903 = term_to_string a  in imp_to_string uu____1903 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____1906 = FStar_Options.print_implicits ()  in
      if uu____1906 then args else filter_imp args  in
    let uu____1910 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1910 (FStar_String.concat " ")

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
    let uu____1926 =
      let uu____1927 = FStar_Options.ugly ()  in Prims.op_Negation uu____1927
       in
    if uu____1926
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1941 =
             let uu____1942 = FStar_Syntax_Subst.compress t  in
             uu____1942.FStar_Syntax_Syntax.n  in
           (match uu____1941 with
            | FStar_Syntax_Syntax.Tm_type uu____1945 when
                let uu____1946 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1946 -> term_to_string t
            | uu____1947 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1949 = univ_to_string u  in
                     let uu____1950 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____1949 uu____1950
                 | uu____1951 ->
                     let uu____1954 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____1954))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1965 =
             let uu____1966 = FStar_Syntax_Subst.compress t  in
             uu____1966.FStar_Syntax_Syntax.n  in
           (match uu____1965 with
            | FStar_Syntax_Syntax.Tm_type uu____1969 when
                let uu____1970 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1970 -> term_to_string t
            | uu____1971 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1973 = univ_to_string u  in
                     let uu____1974 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____1973 uu____1974
                 | uu____1975 ->
                     let uu____1978 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____1978))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1981 = FStar_Options.print_effect_args ()  in
             if uu____1981
             then
               let uu____1982 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____1983 =
                 let uu____1984 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____1984 (FStar_String.concat ", ")
                  in
               let uu____1991 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____1992 =
                 let uu____1993 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____1993 (FStar_String.concat ", ")
                  in
               let uu____2012 =
                 let uu____2013 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2013 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1982
                 uu____1983 uu____1991 uu____1992 uu____2012
             else
               (let uu____2023 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___74_2027  ->
                           match uu___74_2027 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2028 -> false)))
                    &&
                    (let uu____2030 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2030)
                   in
                if uu____2023
                then
                  let uu____2031 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2031
                else
                  (let uu____2033 =
                     ((let uu____2036 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2036) &&
                        (let uu____2038 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2038))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2033
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2040 =
                        (let uu____2043 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2043) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___75_2047  ->
                                   match uu___75_2047 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2048 -> false)))
                         in
                      if uu____2040
                      then
                        let uu____2049 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2049
                      else
                        (let uu____2051 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2052 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2051 uu____2052))))
              in
           let dec =
             let uu____2054 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___76_2064  ->
                       match uu___76_2064 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2070 =
                             let uu____2071 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2071
                              in
                           [uu____2070]
                       | uu____2072 -> []))
                in
             FStar_All.pipe_right uu____2054 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2076 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___77_2082  ->
    match uu___77_2082 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2095 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2125 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2143  ->
                              match uu____2143 with
                              | (t,uu____2149) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2125
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2095 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2155 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2155
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2158) ->
        let uu____2159 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2159
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2167 = sli m  in
        let uu____2168 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2167 uu____2168
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2176 = sli m  in
        let uu____2177 = sli m'  in
        let uu____2178 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2176
          uu____2177 uu____2178
    | FStar_Syntax_Syntax.Meta_quoted (qt,qi) ->
        let uu____2185 =
          let uu____2186 = term_to_string qt  in Prims.strcat uu____2186 ")"
           in
        Prims.strcat "`(" uu____2185

let (binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json) =
  fun env  ->
    fun b  ->
      let uu____2193 = b  in
      match uu____2193 with
      | (a,imp) ->
          let n1 =
            let uu____2197 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2197
            then FStar_Util.JsonNull
            else
              (let uu____2199 =
                 let uu____2200 = nm_to_string a  in
                 imp_to_string uu____2200 imp  in
               FStar_Util.JsonStr uu____2199)
             in
          let t =
            let uu____2202 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2202  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2221 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2221
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2227 = FStar_Options.print_universes ()  in
    if uu____2227 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2232 =
      let uu____2233 = FStar_Options.ugly ()  in Prims.op_Negation uu____2233
       in
    if uu____2232
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2237 = s  in
       match uu____2237 with
       | (us,t) ->
           let uu____2244 =
             let uu____2245 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2245  in
           let uu____2246 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2244 uu____2246)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2250 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2251 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2252 =
      let uu____2253 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2253  in
    let uu____2254 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2255 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2250 uu____2251 uu____2252
      uu____2254 uu____2255
  
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
          let uu____2272 =
            let uu____2273 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2273  in
          if uu____2272
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2285 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2285 (FStar_String.concat ",\n\t")
                in
             let uu____2294 =
               let uu____2297 =
                 let uu____2300 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2301 =
                   let uu____2304 =
                     let uu____2305 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2305  in
                   let uu____2306 =
                     let uu____2309 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2310 =
                       let uu____2313 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2314 =
                         let uu____2317 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2318 =
                           let uu____2321 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2322 =
                             let uu____2325 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2326 =
                               let uu____2329 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2330 =
                                 let uu____2333 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2334 =
                                   let uu____2337 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2338 =
                                     let uu____2341 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2342 =
                                       let uu____2345 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2346 =
                                         let uu____2349 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2350 =
                                           let uu____2353 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2354 =
                                             let uu____2357 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2358 =
                                               let uu____2361 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2362 =
                                                 let uu____2365 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2366 =
                                                   let uu____2369 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2369]  in
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
                     uu____2309 :: uu____2310  in
                   uu____2304 :: uu____2306  in
                 uu____2300 :: uu____2301  in
               (if for_free then "_for_free " else "") :: uu____2297  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2294)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2380 =
      let uu____2381 = FStar_Options.ugly ()  in Prims.op_Negation uu____2381
       in
    if uu____2380
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2387 -> ""
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
             (lid,univs1,tps,k,uu____2398,uu____2399) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2411 = FStar_Options.print_universes ()  in
             if uu____2411
             then
               let uu____2412 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2412 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2417,uu____2418,uu____2419) ->
             let uu____2424 = FStar_Options.print_universes ()  in
             if uu____2424
             then
               let uu____2425 = univ_names_to_string univs1  in
               let uu____2426 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2425
                 lid.FStar_Ident.str uu____2426
             else
               (let uu____2428 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2428)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2432 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2433 =
               let uu____2434 = FStar_Options.print_universes ()  in
               if uu____2434
               then
                 let uu____2435 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2435
               else ""  in
             let uu____2437 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2432
               lid.FStar_Ident.str uu____2433 uu____2437
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2439,f) ->
             let uu____2441 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2441
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2443) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2449 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2449
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2451) ->
             let uu____2460 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2460 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2478) -> lift_wp
               | (uu____2485,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2493 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2493 with
              | (us,t) ->
                  let uu____2504 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2505 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2506 = univ_names_to_string us  in
                  let uu____2507 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2504 uu____2505 uu____2506 uu____2507)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2517 = FStar_Options.print_universes ()  in
             if uu____2517
             then
               let uu____2518 =
                 let uu____2523 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2523  in
               (match uu____2518 with
                | (univs2,t) ->
                    let uu____2526 =
                      let uu____2539 =
                        let uu____2540 = FStar_Syntax_Subst.compress t  in
                        uu____2540.FStar_Syntax_Syntax.n  in
                      match uu____2539 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2581 -> failwith "impossible"  in
                    (match uu____2526 with
                     | (tps1,c1) ->
                         let uu____2612 = sli l  in
                         let uu____2613 = univ_names_to_string univs2  in
                         let uu____2614 = binders_to_string " " tps1  in
                         let uu____2615 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2612 uu____2613 uu____2614 uu____2615))
             else
               (let uu____2617 = sli l  in
                let uu____2618 = binders_to_string " " tps  in
                let uu____2619 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2617 uu____2618
                  uu____2619)
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2620 ->
           let uu____2623 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2623 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2630 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2630 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2634,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2636;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2638;
                       FStar_Syntax_Syntax.lbdef = uu____2639;
                       FStar_Syntax_Syntax.lbattrs = uu____2640;
                       FStar_Syntax_Syntax.lbpos = uu____2641;_}::[]),uu____2642)
        ->
        let uu____2669 = lbname_to_string lb  in
        let uu____2670 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2669 uu____2670
    | uu____2671 ->
        let uu____2672 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2672 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2686 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2687 =
      let uu____2688 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2688 (FStar_String.concat "\n")  in
    let uu____2693 =
      let uu____2694 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2694 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2686 uu____2687 uu____2693
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___78_2701  ->
    match uu___78_2701 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2704 = FStar_Util.string_of_int i  in
        let uu____2705 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2704 uu____2705
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2708 = bv_to_string x  in
        let uu____2709 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2708 uu____2709
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2716 = bv_to_string x  in
        let uu____2717 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2716 uu____2717
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2720 = FStar_Util.string_of_int i  in
        let uu____2721 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2720 uu____2721
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2724 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2724
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2728 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2728 (FStar_String.concat "; ")
  
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
           (let uu____2796 = f x  in
            FStar_Util.string_builder_append strb uu____2796);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2803 = f x1  in
                 FStar_Util.string_builder_append strb uu____2803)) xs;
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
           (let uu____2836 = f x  in
            FStar_Util.string_builder_append strb uu____2836);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2843 = f x1  in
                 FStar_Util.string_builder_append strb uu____2843)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____2855 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____2855
  