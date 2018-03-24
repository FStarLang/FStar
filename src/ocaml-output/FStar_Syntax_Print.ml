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
    | FStar_Syntax_Syntax.Tm_quoted uu____862 -> "Tm_quoted"
    | FStar_Syntax_Syntax.Tm_abs uu____869 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____886 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____899 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____906 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____921 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____944 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____971 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____984 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1001,m) ->
        let uu____1043 = FStar_ST.op_Bang m  in
        (match uu____1043 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1099 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1104,m) ->
        let uu____1110 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1110
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1111 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1113 =
      let uu____1114 = FStar_Options.ugly ()  in Prims.op_Negation uu____1114
       in
    if uu____1113
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1120 = FStar_Options.print_implicits ()  in
         if uu____1120 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1122 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1147,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1167 =
             let uu____1168 =
               let uu____1173 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1173  in
             uu____1168 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1167
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1216;_})
           ->
           let uu____1231 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1231
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1233;_})
           ->
           let uu____1248 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1248
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1266 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1296 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1314  ->
                                 match uu____1314 with
                                 | (t1,uu____1320) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1296
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1266 (FStar_String.concat "\\/")  in
           let uu____1325 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1325
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1337 = tag_of_term t  in
           let uu____1338 = sli m  in
           let uu____1339 = term_to_string t'  in
           let uu____1340 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1337 uu____1338
             uu____1339 uu____1340
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1353 = tag_of_term t  in
           let uu____1354 = term_to_string t'  in
           let uu____1355 = sli m0  in
           let uu____1356 = sli m1  in
           let uu____1357 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1353
             uu____1354 uu____1355 uu____1356 uu____1357
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1366 = FStar_Range.string_of_range r  in
           let uu____1367 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1366
             uu____1367
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1374 = lid_to_string l  in
           let uu____1375 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1376 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1374 uu____1375
             uu____1376
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1378) ->
           let uu____1383 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1383
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1385 = db_to_string x3  in
           let uu____1386 =
             let uu____1387 =
               let uu____1388 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1388 ")"  in
             Prims.strcat ":(" uu____1387  in
           Prims.strcat uu____1385 uu____1386
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1392) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1419 = FStar_Options.print_universes ()  in
           if uu____1419
           then
             let uu____1420 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1420
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1440 = binders_to_string " -> " bs  in
           let uu____1441 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1440 uu____1441
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1466 = binders_to_string " " bs  in
                let uu____1467 = term_to_string t2  in
                let uu____1468 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1472 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1472)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1466 uu____1467
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1468
            | uu____1475 ->
                let uu____1478 = binders_to_string " " bs  in
                let uu____1479 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1478 uu____1479)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1486 = bv_to_string xt  in
           let uu____1487 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1490 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1486 uu____1487 uu____1490
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1515 = term_to_string t  in
           let uu____1516 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1515 uu____1516
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1535 = lbs_to_string [] lbs  in
           let uu____1536 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1535 uu____1536
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1597 =
                   let uu____1598 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1598
                     (FStar_Util.dflt "default")
                    in
                 let uu____1603 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1597 uu____1603
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1619 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1619
              in
           let uu____1620 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1620 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1659 = term_to_string head1  in
           let uu____1660 =
             let uu____1661 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1697  ->
                       match uu____1697 with
                       | (p,wopt,e) ->
                           let uu____1713 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1714 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1716 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1716
                              in
                           let uu____1717 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1713
                             uu____1714 uu____1717))
                in
             FStar_Util.concat_l "\n\t|" uu____1661  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1659 uu____1660
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1724 = FStar_Options.print_universes ()  in
           if uu____1724
           then
             let uu____1725 = term_to_string t  in
             let uu____1726 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1725 uu____1726
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1729 =
      let uu____1730 = FStar_Options.ugly ()  in Prims.op_Negation uu____1730
       in
    if uu____1729
    then
      let e =
        let uu____1732 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1732  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1755 = fv_to_string l  in
           let uu____1756 =
             let uu____1757 =
               FStar_List.map
                 (fun uu____1768  ->
                    match uu____1768 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1757 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1755 uu____1756
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1780) ->
           let uu____1785 = FStar_Options.print_bound_var_types ()  in
           if uu____1785
           then
             let uu____1786 = bv_to_string x1  in
             let uu____1787 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1786 uu____1787
           else
             (let uu____1789 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1789)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1791 = FStar_Options.print_bound_var_types ()  in
           if uu____1791
           then
             let uu____1792 = bv_to_string x1  in
             let uu____1793 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1792 uu____1793
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1797 = FStar_Options.print_real_names ()  in
           if uu____1797
           then
             let uu____1798 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1798
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1810 = quals_to_string' quals  in
      let uu____1811 =
        let uu____1812 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1828 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1829 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1830 =
                    let uu____1831 = FStar_Options.print_universes ()  in
                    if uu____1831
                    then
                      let uu____1832 =
                        let uu____1833 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1833 ">"  in
                      Prims.strcat "<" uu____1832
                    else ""  in
                  let uu____1835 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1836 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1828
                    uu____1829 uu____1830 uu____1835 uu____1836))
           in
        FStar_Util.concat_l "\n and " uu____1812  in
      FStar_Util.format3 "%slet %s %s" uu____1810
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1811

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___71_1842  ->
    match uu___71_1842 with
    | [] -> ""
    | tms ->
        let uu____1848 =
          let uu____1849 =
            FStar_List.map
              (fun t  ->
                 let uu____1855 = term_to_string t  in paren uu____1855) tms
             in
          FStar_All.pipe_right uu____1849 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1848

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____1859 = FStar_Options.print_effect_args ()  in
    if uu____1859
    then
      let uu____1860 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1860
    else
      (let uu____1862 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1863 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1862 uu____1863)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___72_1864  ->
    match uu___72_1864 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1865 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____1868 = aqual_to_string aq  in Prims.strcat uu____1868 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____1871 =
        let uu____1872 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1872  in
      if uu____1871
      then
        let uu____1873 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1873 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1879 = b  in
         match uu____1879 with
         | (a,imp) ->
             let uu____1882 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1882
             then
               let uu____1883 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1883
             else
               (let uu____1885 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1887 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1887)
                   in
                if uu____1885
                then
                  let uu____1888 = nm_to_string a  in
                  imp_to_string uu____1888 imp
                else
                  (let uu____1890 =
                     let uu____1891 = nm_to_string a  in
                     let uu____1892 =
                       let uu____1893 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1893  in
                     Prims.strcat uu____1891 uu____1892  in
                   imp_to_string uu____1890 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1899 = FStar_Options.print_implicits ()  in
        if uu____1899 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1901 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1901 (FStar_String.concat sep)
      else
        (let uu____1909 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1909 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___73_1916  ->
    match uu___73_1916 with
    | (a,imp) ->
        let uu____1923 = term_to_string a  in imp_to_string uu____1923 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____1926 = FStar_Options.print_implicits ()  in
      if uu____1926 then args else filter_imp args  in
    let uu____1930 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1930 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____1943 = FStar_Options.ugly ()  in
      if uu____1943
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____1948 =
      let uu____1949 = FStar_Options.ugly ()  in Prims.op_Negation uu____1949
       in
    if uu____1948
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1963 =
             let uu____1964 = FStar_Syntax_Subst.compress t  in
             uu____1964.FStar_Syntax_Syntax.n  in
           (match uu____1963 with
            | FStar_Syntax_Syntax.Tm_type uu____1967 when
                let uu____1968 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1968 -> term_to_string t
            | uu____1969 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1971 = univ_to_string u  in
                     let uu____1972 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____1971 uu____1972
                 | uu____1973 ->
                     let uu____1976 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____1976))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1987 =
             let uu____1988 = FStar_Syntax_Subst.compress t  in
             uu____1988.FStar_Syntax_Syntax.n  in
           (match uu____1987 with
            | FStar_Syntax_Syntax.Tm_type uu____1991 when
                let uu____1992 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1992 -> term_to_string t
            | uu____1993 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1995 = univ_to_string u  in
                     let uu____1996 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____1995 uu____1996
                 | uu____1997 ->
                     let uu____2000 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2000))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2003 = FStar_Options.print_effect_args ()  in
             if uu____2003
             then
               let uu____2004 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2005 =
                 let uu____2006 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2006 (FStar_String.concat ", ")
                  in
               let uu____2013 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2014 =
                 let uu____2015 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2015 (FStar_String.concat ", ")
                  in
               let uu____2034 =
                 let uu____2035 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2035 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2004
                 uu____2005 uu____2013 uu____2014 uu____2034
             else
               (let uu____2045 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___74_2049  ->
                           match uu___74_2049 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2050 -> false)))
                    &&
                    (let uu____2052 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2052)
                   in
                if uu____2045
                then
                  let uu____2053 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2053
                else
                  (let uu____2055 =
                     ((let uu____2058 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2058) &&
                        (let uu____2060 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2060))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2055
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2062 =
                        (let uu____2065 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2065) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___75_2069  ->
                                   match uu___75_2069 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2070 -> false)))
                         in
                      if uu____2062
                      then
                        let uu____2071 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2071
                      else
                        (let uu____2073 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2074 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2073 uu____2074))))
              in
           let dec =
             let uu____2076 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___76_2086  ->
                       match uu___76_2086 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2092 =
                             let uu____2093 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2093
                              in
                           [uu____2092]
                       | uu____2094 -> []))
                in
             FStar_All.pipe_right uu____2076 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2098 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___77_2104  ->
    match uu___77_2104 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2117 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2147 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2165  ->
                              match uu____2165 with
                              | (t,uu____2171) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2147
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2117 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2177 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2177
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2180) ->
        let uu____2181 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2181
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2189 = sli m  in
        let uu____2190 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2189 uu____2190
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2198 = sli m  in
        let uu____2199 = sli m'  in
        let uu____2200 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2198
          uu____2199 uu____2200

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2207 = FStar_Options.ugly ()  in
      if uu____2207
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
      let uu____2217 = b  in
      match uu____2217 with
      | (a,imp) ->
          let n1 =
            let uu____2221 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2221
            then FStar_Util.JsonNull
            else
              (let uu____2223 =
                 let uu____2224 = nm_to_string a  in
                 imp_to_string uu____2224 imp  in
               FStar_Util.JsonStr uu____2223)
             in
          let t =
            let uu____2226 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2226  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2245 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2245
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2251 = FStar_Options.print_universes ()  in
    if uu____2251 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2256 =
      let uu____2257 = FStar_Options.ugly ()  in Prims.op_Negation uu____2257
       in
    if uu____2256
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2261 = s  in
       match uu____2261 with
       | (us,t) ->
           let uu____2268 =
             let uu____2269 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2269  in
           let uu____2270 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2268 uu____2270)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2274 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2275 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2276 =
      let uu____2277 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2277  in
    let uu____2278 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2279 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2274 uu____2275 uu____2276
      uu____2278 uu____2279
  
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
          let uu____2296 =
            let uu____2297 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2297  in
          if uu____2296
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2309 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2309 (FStar_String.concat ",\n\t")
                in
             let uu____2318 =
               let uu____2321 =
                 let uu____2324 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2325 =
                   let uu____2328 =
                     let uu____2329 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2329  in
                   let uu____2330 =
                     let uu____2333 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2334 =
                       let uu____2337 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2338 =
                         let uu____2341 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2342 =
                           let uu____2345 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2346 =
                             let uu____2349 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2350 =
                               let uu____2353 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2354 =
                                 let uu____2357 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2358 =
                                   let uu____2361 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2362 =
                                     let uu____2365 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2366 =
                                       let uu____2369 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2370 =
                                         let uu____2373 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2374 =
                                           let uu____2377 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2378 =
                                             let uu____2381 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2382 =
                                               let uu____2385 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2386 =
                                                 let uu____2389 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2390 =
                                                   let uu____2393 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2393]  in
                                                 uu____2389 :: uu____2390  in
                                               uu____2385 :: uu____2386  in
                                             uu____2381 :: uu____2382  in
                                           uu____2377 :: uu____2378  in
                                         uu____2373 :: uu____2374  in
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
                   uu____2328 :: uu____2330  in
                 uu____2324 :: uu____2325  in
               (if for_free then "_for_free " else "") :: uu____2321  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2318)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2404 =
      let uu____2405 = FStar_Options.ugly ()  in Prims.op_Negation uu____2405
       in
    if uu____2404
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2411 -> ""
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
             (lid,univs1,tps,k,uu____2422,uu____2423) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2435 = FStar_Options.print_universes ()  in
             if uu____2435
             then
               let uu____2436 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2436 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2441,uu____2442,uu____2443) ->
             let uu____2448 = FStar_Options.print_universes ()  in
             if uu____2448
             then
               let uu____2449 = univ_names_to_string univs1  in
               let uu____2450 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2449
                 lid.FStar_Ident.str uu____2450
             else
               (let uu____2452 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2452)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2456 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2457 =
               let uu____2458 = FStar_Options.print_universes ()  in
               if uu____2458
               then
                 let uu____2459 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2459
               else ""  in
             let uu____2461 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2456
               lid.FStar_Ident.str uu____2457 uu____2461
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2463,f) ->
             let uu____2465 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2465
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2467) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2473 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2473
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2475) ->
             let uu____2484 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2484 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2502) -> lift_wp
               | (uu____2509,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2517 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2517 with
              | (us,t) ->
                  let uu____2528 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2529 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2530 = univ_names_to_string us  in
                  let uu____2531 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2528 uu____2529 uu____2530 uu____2531)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2541 = FStar_Options.print_universes ()  in
             if uu____2541
             then
               let uu____2542 =
                 let uu____2547 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2547  in
               (match uu____2542 with
                | (univs2,t) ->
                    let uu____2550 =
                      let uu____2563 =
                        let uu____2564 = FStar_Syntax_Subst.compress t  in
                        uu____2564.FStar_Syntax_Syntax.n  in
                      match uu____2563 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2605 -> failwith "impossible"  in
                    (match uu____2550 with
                     | (tps1,c1) ->
                         let uu____2636 = sli l  in
                         let uu____2637 = univ_names_to_string univs2  in
                         let uu____2638 = binders_to_string " " tps1  in
                         let uu____2639 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2636 uu____2637 uu____2638 uu____2639))
             else
               (let uu____2641 = sli l  in
                let uu____2642 = binders_to_string " " tps  in
                let uu____2643 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2641 uu____2642
                  uu____2643)
         | FStar_Syntax_Syntax.Sig_splice t ->
             let uu____2645 = term_to_string t  in
             FStar_Util.format1 "splice (%s)" uu____2645
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2646 ->
           let uu____2649 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2649 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2656 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2656 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2660,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2662;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2664;
                       FStar_Syntax_Syntax.lbdef = uu____2665;
                       FStar_Syntax_Syntax.lbattrs = uu____2666;
                       FStar_Syntax_Syntax.lbpos = uu____2667;_}::[]),uu____2668)
        ->
        let uu____2695 = lbname_to_string lb  in
        let uu____2696 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2695 uu____2696
    | uu____2697 ->
        let uu____2698 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2698 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2712 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2713 =
      let uu____2714 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2714 (FStar_String.concat "\n")  in
    let uu____2719 =
      let uu____2720 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2720 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2712 uu____2713 uu____2719
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___78_2727  ->
    match uu___78_2727 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2730 = FStar_Util.string_of_int i  in
        let uu____2731 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2730 uu____2731
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2734 = bv_to_string x  in
        let uu____2735 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2734 uu____2735
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2742 = bv_to_string x  in
        let uu____2743 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2742 uu____2743
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2746 = FStar_Util.string_of_int i  in
        let uu____2747 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2746 uu____2747
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2750 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2750
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2754 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2754 (FStar_String.concat "; ")
  
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
           (let uu____2822 = f x  in
            FStar_Util.string_builder_append strb uu____2822);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2829 = f x1  in
                 FStar_Util.string_builder_append strb uu____2829)) xs;
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
           (let uu____2862 = f x  in
            FStar_Util.string_builder_append strb uu____2862);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2869 = f x1  in
                 FStar_Util.string_builder_append strb uu____2869)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____2881 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____2881
  