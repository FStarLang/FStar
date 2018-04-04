open Prims
let rec delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
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
  
let sli : FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____12 = FStar_Options.print_real_names ()  in
    if uu____12
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let lid_to_string : FStar_Ident.lid -> Prims.string = fun l  -> sli l 
let fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____23 =
      let uu____24 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____24  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____23
  
let nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____28 = FStar_Options.print_real_names ()  in
    if uu____28
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let db_to_string : FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____33 =
      let uu____34 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____34  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____33
  
let infix_prim_ops :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
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
let unary_prim_ops :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  [(FStar_Parser_Const.op_Negation, "not");
  (FStar_Parser_Const.op_Minus, "-");
  (FStar_Parser_Const.not_lid, "~")] 
let is_prim_op :
  FStar_Ident.lident Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool
  =
  fun ps  ->
    fun f  ->
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_All.pipe_right ps
            (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
      | uu____168 -> false
  
let get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____177 -> failwith "get_lid"
  
let is_infix_prim_op : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
  
let is_unary_prim_op : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
  
let quants :
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")] 
type exp = FStar_Syntax_Syntax.term[@@deriving show]
let is_b2t : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Parser_Const.b2t_lid] t 
let is_quant : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t
  
let is_ite : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Parser_Const.ite_lid] t 
let is_lex_cons : exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Parser_Const.lexcons_lid] f 
let is_lex_top : exp -> Prims.bool =
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
  
let rec reconstruct_lex :
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option
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
  
let find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____523 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____523
  
let infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____545 = get_lid e  in find_lid uu____545 infix_prim_ops 
let unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____553 = get_lid e  in find_lid uu____553 unary_prim_ops 
let quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun t  -> let uu____561 = get_lid t  in find_lid uu____561 quants 
let const_to_string : FStar_Const.sconst -> Prims.string =
  fun x  -> FStar_Parser_Const.const_to_string x 
let lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___71_567  ->
    match uu___71_567 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____573 = FStar_Options.hide_uvar_nums ()  in
    if uu____573
    then "?"
    else
      (let uu____575 =
         let uu____576 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____576 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____575)
  
let version_to_string : FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____580 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____581 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____580 uu____581
  
let univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string =
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
  
let rec int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____608 = FStar_Syntax_Subst.compress_univ u  in
      match uu____608 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____618 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string =
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
  
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____675 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____675 (FStar_String.concat ", ")
  
let univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string =
  fun us  ->
    let uu____683 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____683 (FStar_String.concat ", ")
  
let qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string =
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
  
let quals_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____752 ->
        let uu____755 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____755 (FStar_String.concat " ")
  
let quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____771 ->
        let uu____774 = quals_to_string quals  in Prims.strcat uu____774 " "
  
let paren : Prims.string -> Prims.string =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec tag_of_term : FStar_Syntax_Syntax.term -> Prims.string =
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
    | FStar_Syntax_Syntax.Tm_quoted uu____858 -> "Tm_quoted"
    | FStar_Syntax_Syntax.Tm_abs uu____865 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____882 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____895 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____902 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____917 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____940 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____967 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____980 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____997,m) ->
        let uu____1039 = FStar_ST.op_Bang m  in
        (match uu____1039 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1095 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1100,m) ->
        let uu____1106 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1106
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1107 -> "Tm_lazy"

and term_to_string : FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1109 =
      let uu____1110 = FStar_Options.ugly ()  in Prims.op_Negation uu____1110
       in
    if uu____1109
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1116 = FStar_Options.print_implicits ()  in
         if uu____1116 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1118 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1143,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1163 =
             let uu____1164 =
               let uu____1169 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1169  in
             uu____1164 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1163
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1212;_})
           ->
           let uu____1227 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1227
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1229;_})
           ->
           let uu____1244 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1244
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1262 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1292 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1310  ->
                                 match uu____1310 with
                                 | (t1,uu____1316) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1292
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1262 (FStar_String.concat "\\/")  in
           let uu____1321 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1321
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1333 = tag_of_term t  in
           let uu____1334 = sli m  in
           let uu____1335 = term_to_string t'  in
           let uu____1336 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1333 uu____1334
             uu____1335 uu____1336
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1349 = tag_of_term t  in
           let uu____1350 = term_to_string t'  in
           let uu____1351 = sli m0  in
           let uu____1352 = sli m1  in
           let uu____1353 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1349
             uu____1350 uu____1351 uu____1352 uu____1353
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1362 = FStar_Range.string_of_range r  in
           let uu____1363 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1362
             uu____1363
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1370 = lid_to_string l  in
           let uu____1371 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1372 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1370 uu____1371
             uu____1372
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1374) ->
           let uu____1379 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1379
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1381 = db_to_string x3  in
           let uu____1382 =
             let uu____1383 =
               let uu____1384 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1384 ")"  in
             Prims.strcat ":(" uu____1383  in
           Prims.strcat uu____1381 uu____1382
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1388) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1415 = FStar_Options.print_universes ()  in
           if uu____1415
           then
             let uu____1416 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1416
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1436 = binders_to_string " -> " bs  in
           let uu____1437 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1436 uu____1437
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1462 = binders_to_string " " bs  in
                let uu____1463 = term_to_string t2  in
                let uu____1464 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1468 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1468)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1462 uu____1463
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1464
            | uu____1471 ->
                let uu____1474 = binders_to_string " " bs  in
                let uu____1475 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1474 uu____1475)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1482 = bv_to_string xt  in
           let uu____1483 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1486 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1482 uu____1483 uu____1486
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1511 = term_to_string t  in
           let uu____1512 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1511 uu____1512
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1531 = lbs_to_string [] lbs  in
           let uu____1532 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1531 uu____1532
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1593 =
                   let uu____1594 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1594
                     (FStar_Util.dflt "default")
                    in
                 let uu____1599 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1593 uu____1599
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1615 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1615
              in
           let uu____1616 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1616 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1655 = term_to_string head1  in
           let uu____1656 =
             let uu____1657 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1693  ->
                       match uu____1693 with
                       | (p,wopt,e) ->
                           let uu____1709 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1710 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1712 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1712
                              in
                           let uu____1713 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1709
                             uu____1710 uu____1713))
                in
             FStar_Util.concat_l "\n\t|" uu____1657  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1655 uu____1656
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1720 = FStar_Options.print_universes ()  in
           if uu____1720
           then
             let uu____1721 = term_to_string t  in
             let uu____1722 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1721 uu____1722
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1725 =
      let uu____1726 = FStar_Options.ugly ()  in Prims.op_Negation uu____1726
       in
    if uu____1725
    then
      let e =
        let uu____1728 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1728  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1751 = fv_to_string l  in
           let uu____1752 =
             let uu____1753 =
               FStar_List.map
                 (fun uu____1764  ->
                    match uu____1764 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1753 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1751 uu____1752
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1776) ->
           let uu____1781 = FStar_Options.print_bound_var_types ()  in
           if uu____1781
           then
             let uu____1782 = bv_to_string x1  in
             let uu____1783 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1782 uu____1783
           else
             (let uu____1785 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1785)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1787 = FStar_Options.print_bound_var_types ()  in
           if uu____1787
           then
             let uu____1788 = bv_to_string x1  in
             let uu____1789 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1788 uu____1789
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1793 = FStar_Options.print_real_names ()  in
           if uu____1793
           then
             let uu____1794 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1794
           else "_")

and lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1806 = quals_to_string' quals  in
      let uu____1807 =
        let uu____1808 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1824 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____1825 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1826 =
                    let uu____1827 = FStar_Options.print_universes ()  in
                    if uu____1827
                    then
                      let uu____1828 =
                        let uu____1829 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1829 ">"  in
                      Prims.strcat "<" uu____1828
                    else ""  in
                  let uu____1831 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1832 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____1824
                    uu____1825 uu____1826 uu____1831 uu____1832))
           in
        FStar_Util.concat_l "\n and " uu____1808  in
      FStar_Util.format3 "%slet %s %s" uu____1806
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1807

and attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string =
  fun uu___73_1838  ->
    match uu___73_1838 with
    | [] -> ""
    | tms ->
        let uu____1844 =
          let uu____1845 =
            FStar_List.map
              (fun t  ->
                 let uu____1851 = term_to_string t  in paren uu____1851) tms
             in
          FStar_All.pipe_right uu____1845 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____1844

and lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1855 = FStar_Options.print_effect_args ()  in
    if uu____1855
    then
      let uu____1856 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____1856
    else
      (let uu____1858 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1859 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1858 uu____1859)

and aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string =
  fun uu___74_1860  ->
    match uu___74_1860 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____1861 -> ""

and imp_to_string : Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string
  =
  fun s  ->
    fun aq  ->
      let uu____1864 = aqual_to_string aq  in Prims.strcat uu____1864 s

and binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1867 =
        let uu____1868 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1868  in
      if uu____1867
      then
        let uu____1869 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1869 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1875 = b  in
         match uu____1875 with
         | (a,imp) ->
             let uu____1878 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1878
             then
               let uu____1879 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1879
             else
               (let uu____1881 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1883 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1883)
                   in
                if uu____1881
                then
                  let uu____1884 = nm_to_string a  in
                  imp_to_string uu____1884 imp
                else
                  (let uu____1886 =
                     let uu____1887 = nm_to_string a  in
                     let uu____1888 =
                       let uu____1889 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1889  in
                     Prims.strcat uu____1887 uu____1888  in
                   imp_to_string uu____1886 imp)))

and binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b

and arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b

and binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1895 = FStar_Options.print_implicits ()  in
        if uu____1895 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1897 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1897 (FStar_String.concat sep)
      else
        (let uu____1905 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1905 (FStar_String.concat sep))

and arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___75_1912  ->
    match uu___75_1912 with
    | (a,imp) ->
        let uu____1919 = term_to_string a  in imp_to_string uu____1919 imp

and args_to_string : FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1922 = FStar_Options.print_implicits ()  in
      if uu____1922 then args else filter_imp args  in
    let uu____1926 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1926 (FStar_String.concat " ")

and comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string =
  fun env  ->
    fun c  ->
      let uu____1939 = FStar_Options.ugly ()  in
      if uu____1939
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1944 =
      let uu____1945 = FStar_Options.ugly ()  in Prims.op_Negation uu____1945
       in
    if uu____1944
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
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
                     FStar_Util.format2 "Tot<%s> %s" uu____1967 uu____1968
                 | uu____1969 ->
                     let uu____1972 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____1972))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1983 =
             let uu____1984 = FStar_Syntax_Subst.compress t  in
             uu____1984.FStar_Syntax_Syntax.n  in
           (match uu____1983 with
            | FStar_Syntax_Syntax.Tm_type uu____1987 when
                let uu____1988 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1988 -> term_to_string t
            | uu____1989 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1991 = univ_to_string u  in
                     let uu____1992 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____1991 uu____1992
                 | uu____1993 ->
                     let uu____1996 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____1996))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1999 = FStar_Options.print_effect_args ()  in
             if uu____1999
             then
               let uu____2000 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2001 =
                 let uu____2002 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2002 (FStar_String.concat ", ")
                  in
               let uu____2009 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2010 =
                 let uu____2011 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2011 (FStar_String.concat ", ")
                  in
               let uu____2030 =
                 let uu____2031 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2031 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2000
                 uu____2001 uu____2009 uu____2010 uu____2030
             else
               (let uu____2041 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___76_2045  ->
                           match uu___76_2045 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2046 -> false)))
                    &&
                    (let uu____2048 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2048)
                   in
                if uu____2041
                then
                  let uu____2049 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2049
                else
                  (let uu____2051 =
                     ((let uu____2054 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2054) &&
                        (let uu____2056 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2056))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2051
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2058 =
                        (let uu____2061 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2061) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___77_2065  ->
                                   match uu___77_2065 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2066 -> false)))
                         in
                      if uu____2058
                      then
                        let uu____2067 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2067
                      else
                        (let uu____2069 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2070 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2069 uu____2070))))
              in
           let dec =
             let uu____2072 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___78_2082  ->
                       match uu___78_2082 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2088 =
                             let uu____2089 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2089
                              in
                           [uu____2088]
                       | uu____2090 -> []))
                in
             FStar_All.pipe_right uu____2072 (FStar_String.concat " ")  in
           FStar_Util.format2 "%s%s" basic dec)

and cflags_to_string : FStar_Syntax_Syntax.cflags -> Prims.string =
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
    | FStar_Syntax_Syntax.DECREASES uu____2094 -> ""

and formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi

and metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string =
  fun uu___79_2100  ->
    match uu___79_2100 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2113 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2143 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2161  ->
                              match uu____2161 with
                              | (t,uu____2167) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2143
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2113 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2173 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2173
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2176) ->
        let uu____2177 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2177
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2185 = sli m  in
        let uu____2186 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2185 uu____2186
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2194 = sli m  in
        let uu____2195 = sli m'  in
        let uu____2196 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2194
          uu____2195 uu____2196

let term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun env  ->
    fun x  ->
      let uu____2203 = FStar_Options.ugly ()  in
      if uu____2203
      then term_to_string x
      else
        (let e = FStar_Syntax_Resugar.resugar_term' env x  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)
  
let binder_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun env  ->
    fun b  ->
      let uu____2213 = b  in
      match uu____2213 with
      | (a,imp) ->
          let n1 =
            let uu____2217 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2217
            then FStar_Util.JsonNull
            else
              (let uu____2219 =
                 let uu____2220 = nm_to_string a  in
                 imp_to_string uu____2220 imp  in
               FStar_Util.JsonStr uu____2219)
             in
          let t =
            let uu____2222 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2222  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun env  ->
    fun bs  ->
      let uu____2241 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2241
  
let enclose_universes : Prims.string -> Prims.string =
  fun s  ->
    let uu____2247 = FStar_Options.print_universes ()  in
    if uu____2247 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2252 =
      let uu____2253 = FStar_Options.ugly ()  in Prims.op_Negation uu____2253
       in
    if uu____2252
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2257 = s  in
       match uu____2257 with
       | (us,t) ->
           let uu____2264 =
             let uu____2265 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2265  in
           let uu____2266 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2264 uu____2266)
  
let action_to_string : FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2270 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2271 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2272 =
      let uu____2273 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2273  in
    let uu____2274 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2275 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2270 uu____2271 uu____2272
      uu____2274 uu____2275
  
let eff_decl_to_string' :
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____2292 =
            let uu____2293 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2293  in
          if uu____2292
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2305 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2305 (FStar_String.concat ",\n\t")
                in
             let uu____2314 =
               let uu____2317 =
                 let uu____2320 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2321 =
                   let uu____2324 =
                     let uu____2325 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2325  in
                   let uu____2326 =
                     let uu____2329 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2330 =
                       let uu____2333 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2334 =
                         let uu____2337 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2338 =
                           let uu____2341 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2342 =
                             let uu____2345 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2346 =
                               let uu____2349 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2350 =
                                 let uu____2353 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2354 =
                                   let uu____2357 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2358 =
                                     let uu____2361 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2362 =
                                       let uu____2365 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2366 =
                                         let uu____2369 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2370 =
                                           let uu____2373 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2374 =
                                             let uu____2377 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2378 =
                                               let uu____2381 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2382 =
                                                 let uu____2385 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2386 =
                                                   let uu____2389 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2389]  in
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
                     uu____2329 :: uu____2330  in
                   uu____2324 :: uu____2326  in
                 uu____2320 :: uu____2321  in
               (if for_free then "_for_free " else "") :: uu____2317  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2314)
  
let eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2400 =
      let uu____2401 = FStar_Options.ugly ()  in Prims.op_Negation uu____2401
       in
    if uu____2400
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2407 -> ""
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
             (lid,univs1,tps,k,uu____2418,uu____2419) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2431 = FStar_Options.print_universes ()  in
             if uu____2431
             then
               let uu____2432 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2432 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2437,uu____2438,uu____2439) ->
             let uu____2444 = FStar_Options.print_universes ()  in
             if uu____2444
             then
               let uu____2445 = univ_names_to_string univs1  in
               let uu____2446 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2445
                 lid.FStar_Ident.str uu____2446
             else
               (let uu____2448 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2448)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2452 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2453 =
               let uu____2454 = FStar_Options.print_universes ()  in
               if uu____2454
               then
                 let uu____2455 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2455
               else ""  in
             let uu____2457 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2452
               lid.FStar_Ident.str uu____2453 uu____2457
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2459,f) ->
             let uu____2461 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2461
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2463) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2469 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2469
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2471) ->
             let uu____2480 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2480 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2498) -> lift_wp
               | (uu____2505,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2513 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2513 with
              | (us,t) ->
                  let uu____2524 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2525 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2526 = univ_names_to_string us  in
                  let uu____2527 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2524 uu____2525 uu____2526 uu____2527)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2537 = FStar_Options.print_universes ()  in
             if uu____2537
             then
               let uu____2538 =
                 let uu____2543 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2543  in
               (match uu____2538 with
                | (univs2,t) ->
                    let uu____2546 =
                      let uu____2559 =
                        let uu____2560 = FStar_Syntax_Subst.compress t  in
                        uu____2560.FStar_Syntax_Syntax.n  in
                      match uu____2559 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2601 -> failwith "impossible"  in
                    (match uu____2546 with
                     | (tps1,c1) ->
                         let uu____2632 = sli l  in
                         let uu____2633 = univ_names_to_string univs2  in
                         let uu____2634 = binders_to_string " " tps1  in
                         let uu____2635 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2632 uu____2633 uu____2634 uu____2635))
             else
               (let uu____2637 = sli l  in
                let uu____2638 = binders_to_string " " tps  in
                let uu____2639 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2637 uu____2638
                  uu____2639)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2646 =
               let uu____2647 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2647  in
             let uu____2652 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2646 uu____2652
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2653 ->
           let uu____2656 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2656 (Prims.strcat "\n" basic))
  
let format_error : FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2663 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2663 msg
  
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2667,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2669;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2671;
                       FStar_Syntax_Syntax.lbdef = uu____2672;
                       FStar_Syntax_Syntax.lbattrs = uu____2673;
                       FStar_Syntax_Syntax.lbpos = uu____2674;_}::[]),uu____2675)
        ->
        let uu____2702 = lbname_to_string lb  in
        let uu____2703 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2702 uu____2703
    | uu____2704 ->
        let uu____2705 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2705 (FStar_String.concat ", ")
  
let rec modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2719 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2720 =
      let uu____2721 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2721 (FStar_String.concat "\n")  in
    let uu____2726 =
      let uu____2727 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2727 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2719 uu____2720 uu____2726
  
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___80_2734  ->
    match uu___80_2734 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2737 = FStar_Util.string_of_int i  in
        let uu____2738 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2737 uu____2738
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2741 = bv_to_string x  in
        let uu____2742 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2741 uu____2742
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2749 = bv_to_string x  in
        let uu____2750 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2749 uu____2750
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2753 = FStar_Util.string_of_int i  in
        let uu____2754 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2753 uu____2754
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2757 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2757
  
let subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2761 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2761 (FStar_String.concat "; ")
  
let abs_ascription_to_string :
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
    FStar_Pervasives_Native.option -> Prims.string
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder ()  in
    (match ascription with
     | FStar_Pervasives_Native.None  ->
         FStar_Util.string_builder_append strb "None"
     | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____2795 =
             FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
           FStar_Util.string_builder_append strb uu____2795))
     | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
         (FStar_Util.string_builder_append strb "Some Inr ";
          (let uu____2802 = FStar_Ident.text_of_lid lid  in
           FStar_Util.string_builder_append strb uu____2802)));
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
           (let uu____2831 = f x  in
            FStar_Util.string_builder_append strb uu____2831);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2838 = f x1  in
                 FStar_Util.string_builder_append strb uu____2838)) xs;
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
           (let uu____2871 = f x  in
            FStar_Util.string_builder_append strb uu____2871);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2878 = f x1  in
                 FStar_Util.string_builder_append strb uu____2878)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  
let bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string =
  fun sep  ->
    fun bvs  ->
      let uu____2890 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____2890
  