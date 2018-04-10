open Prims
let rec (delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string) =
  fun uu___68_5  ->
    match uu___68_5 with
    | FStar_Syntax_Syntax.Delta_constant  -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____7 = FStar_Util.string_of_int i  in
        Prims.strcat "Delta_defined_at_level " uu____7
    | FStar_Syntax_Syntax.Delta_equational  -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____9 =
          let uu____10 = delta_depth_to_string d  in
          Prims.strcat uu____10 ")"  in
        Prims.strcat "Delta_abstract (" uu____9
  
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____16 = FStar_Options.print_real_names ()  in
    if uu____16
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (lid_to_string : FStar_Ident.lid -> Prims.string) = fun l  -> sli l 
let (fv_to_string : FStar_Syntax_Syntax.fv -> Prims.string) =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (bv_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____33 =
      let uu____34 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "#" uu____34  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____33
  
let (nm_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____40 = FStar_Options.print_real_names ()  in
    if uu____40
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (db_to_string : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun bv  ->
    let uu____47 =
      let uu____48 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index
         in
      Prims.strcat "@" uu____48  in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____47
  
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
      | uu____186 -> false
  
let (get_lid :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____197 -> failwith "get_lid"
  
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
  'Auu____269 'Auu____270 .
    ('Auu____269,'Auu____270) FStar_Util.either -> Prims.bool
  =
  fun uu___69_279  ->
    match uu___69_279 with
    | FStar_Util.Inl uu____284 -> false
    | FStar_Util.Inr uu____285 -> true
  
let filter_imp :
  'Auu____290 .
    ('Auu____290,FStar_Syntax_Syntax.arg_qualifier
                   FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      ('Auu____290,FStar_Syntax_Syntax.arg_qualifier
                     FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a  ->
    FStar_All.pipe_right a
      (FStar_List.filter
         (fun uu___70_345  ->
            match uu___70_345 with
            | (uu____352,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____353)) -> false
            | uu____356 -> true))
  
let rec (reconstruct_lex :
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____374 =
      let uu____375 = FStar_Syntax_Subst.compress e  in
      uu____375.FStar_Syntax_Syntax.n  in
    match uu____374 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args  in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1  in
        let uu____438 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2"))
           in
        if uu____438
        then
          let uu____447 =
            let uu____454 = FStar_List.nth exps (Prims.parse_int "1")  in
            reconstruct_lex uu____454  in
          (match uu____447 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____472 =
                 let uu____477 = FStar_List.nth exps (Prims.parse_int "0")
                    in
                 uu____477 :: xs  in
               FStar_Pervasives_Native.Some uu____472
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____501 ->
        let uu____502 = is_lex_top e  in
        if uu____502
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
  
let rec find : 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____551 = f hd1  in if uu____551 then hd1 else find f tl1
  
let (find_lid :
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string)
  =
  fun x  ->
    fun xs  ->
      let uu____575 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs
         in
      FStar_Pervasives_Native.snd uu____575
  
let (infix_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____599 = get_lid e  in find_lid uu____599 infix_prim_ops 
let (unary_prim_op_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun e  -> let uu____609 = get_lid e  in find_lid uu____609 unary_prim_ops 
let (quant_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun t  -> let uu____619 = get_lid t  in find_lid uu____619 quants 
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  -> FStar_Parser_Const.const_to_string x 
let (lbname_to_string : FStar_Syntax_Syntax.lbname -> Prims.string) =
  fun uu___71_629  ->
    match uu___71_629 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let (uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string) =
  fun u  ->
    let uu____637 = FStar_Options.hide_uvar_nums ()  in
    if uu____637
    then "?"
    else
      (let uu____639 =
         let uu____640 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____640 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____639)
  
let (version_to_string : FStar_Syntax_Syntax.version -> Prims.string) =
  fun v1  ->
    let uu____646 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____647 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____646 uu____647
  
let (univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string)
  =
  fun u  ->
    let uu____653 = FStar_Options.hide_uvar_nums ()  in
    if uu____653
    then "?"
    else
      (let uu____655 =
         let uu____656 =
           let uu____657 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____657 FStar_Util.string_of_int  in
         let uu____658 =
           let uu____659 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____659  in
         Prims.strcat uu____656 uu____658  in
       Prims.strcat "?" uu____655)
  
let rec (int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun n1  ->
    fun u  ->
      let uu____680 = FStar_Syntax_Subst.compress_univ u  in
      match uu____680 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____690 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec (univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string) =
  fun u  ->
    let uu____698 =
      let uu____699 = FStar_Options.ugly ()  in Prims.op_Negation uu____699
       in
    if uu____698
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____703 = FStar_Syntax_Subst.compress_univ u  in
       match uu____703 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____715 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____715
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____717 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____717 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____731 = univ_to_string u2  in
                let uu____732 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____731 uu____732)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____736 =
             let uu____737 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____737 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____736
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let (univs_to_string :
  FStar_Syntax_Syntax.universe Prims.list -> Prims.string) =
  fun us  ->
    let uu____751 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____751 (FStar_String.concat ", ")
  
let (univ_names_to_string : FStar_Syntax_Syntax.univ_names -> Prims.string) =
  fun us  ->
    let uu____761 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____761 (FStar_String.concat ", ")
  
let (qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string) =
  fun uu___72_772  ->
    match uu___72_772 with
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
        let uu____774 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____774
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____777 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____777 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____788 =
          let uu____789 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____789  in
        let uu____790 =
          let uu____791 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____791 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____788 uu____790
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____810 =
          let uu____811 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____811  in
        let uu____812 =
          let uu____813 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____813 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____810 uu____812
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____823 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____823
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
    | uu____834 ->
        let uu____837 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____837 (FStar_String.concat " ")
  
let (quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string) =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____855 ->
        let uu____858 = quals_to_string quals  in Prims.strcat uu____858 " "
  
let (paren : Prims.string -> Prims.string) =
  fun s  -> Prims.strcat "(" (Prims.strcat s ")") 
let rec (tag_of_term : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____978 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____978
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____980 = nm_to_string x  in Prims.strcat "Tm_name: " uu____980
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____982 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____982
    | FStar_Syntax_Syntax.Tm_uinst uu____983 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____990 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____991 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____992,{
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static ;
                     FStar_Syntax_Syntax.antiquotes = uu____993;_})
        -> "Tm_quoted (static)"
    | FStar_Syntax_Syntax.Tm_quoted
        (uu____1008,{
                      FStar_Syntax_Syntax.qkind =
                        FStar_Syntax_Syntax.Quote_dynamic ;
                      FStar_Syntax_Syntax.antiquotes = uu____1009;_})
        -> "Tm_quoted (dynamic)"
    | FStar_Syntax_Syntax.Tm_abs uu____1024 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____1041 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____1054 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____1061 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____1076 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____1099 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____1126 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____1139 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____1156,m) ->
        let uu____1198 = FStar_ST.op_Bang m  in
        (match uu____1198 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____1258 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta (uu____1263,m) ->
        let uu____1269 = metadata_to_string m  in
        Prims.strcat "Tm_meta:" uu____1269
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
    | FStar_Syntax_Syntax.Tm_lazy uu____1270 -> "Tm_lazy"

and (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun x  ->
    let uu____1272 =
      let uu____1273 = FStar_Options.ugly ()  in Prims.op_Negation uu____1273
       in
    if uu____1272
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1279 = FStar_Options.print_implicits ()  in
         if uu____1279 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1281 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1306,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu____1326 =
             let uu____1327 =
               let uu____1334 =
                 FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
               FStar_Util.must uu____1334  in
             uu____1327 i.FStar_Syntax_Syntax.lkind i  in
           term_to_string uu____1326
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static ;
                 FStar_Syntax_Syntax.antiquotes = uu____1389;_})
           ->
           let uu____1404 = term_to_string tm  in
           FStar_Util.format1 "`(%s)" uu____1404
       | FStar_Syntax_Syntax.Tm_quoted
           (tm,{
                 FStar_Syntax_Syntax.qkind =
                   FStar_Syntax_Syntax.Quote_dynamic ;
                 FStar_Syntax_Syntax.antiquotes = uu____1406;_})
           ->
           let uu____1421 = term_to_string tm  in
           FStar_Util.format1 "quote (%s)" uu____1421
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1439 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1469 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1487  ->
                                 match uu____1487 with
                                 | (t1,uu____1493) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1469
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1439 (FStar_String.concat "\\/")  in
           let uu____1498 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1498
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1510 = tag_of_term t  in
           let uu____1511 = sli m  in
           let uu____1512 = term_to_string t'  in
           let uu____1513 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1510 uu____1511
             uu____1512 uu____1513
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1526 = tag_of_term t  in
           let uu____1527 = term_to_string t'  in
           let uu____1528 = sli m0  in
           let uu____1529 = sli m1  in
           let uu____1530 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1526
             uu____1527 uu____1528 uu____1529 uu____1530
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1539 = FStar_Range.string_of_range r  in
           let uu____1540 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1539
             uu____1540
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1547 = lid_to_string l  in
           let uu____1548 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1549 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1547 uu____1548
             uu____1549
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1551) ->
           let uu____1556 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1556
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1558 = db_to_string x3  in
           let uu____1559 =
             let uu____1560 =
               let uu____1561 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1561 ")"  in
             Prims.strcat ":(" uu____1560  in
           Prims.strcat uu____1558 uu____1559
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1565) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1592 = FStar_Options.print_universes ()  in
           if uu____1592
           then
             let uu____1593 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1593
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1613 = binders_to_string " -> " bs  in
           let uu____1614 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1613 uu____1614
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1639 = binders_to_string " " bs  in
                let uu____1640 = term_to_string t2  in
                let uu____1641 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1645 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1645)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1639 uu____1640
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1641
            | uu____1648 ->
                let uu____1651 = binders_to_string " " bs  in
                let uu____1652 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1651 uu____1652)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1659 = bv_to_string xt  in
           let uu____1660 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1663 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1659 uu____1660 uu____1663
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1688 = term_to_string t  in
           let uu____1689 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1688 uu____1689
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1708 = lbs_to_string [] lbs  in
           let uu____1709 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1708 uu____1709
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1770 =
                   let uu____1771 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1771
                     (FStar_Util.dflt "default")
                    in
                 let uu____1776 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1770 uu____1776
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1792 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1792
              in
           let uu____1793 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1793 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1832 = term_to_string head1  in
           let uu____1833 =
             let uu____1834 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1870  ->
                       match uu____1870 with
                       | (p,wopt,e) ->
                           let uu____1886 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1887 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1889 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1889
                              in
                           let uu____1890 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1886
                             uu____1887 uu____1890))
                in
             FStar_Util.concat_l "\n\t|" uu____1834  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1832 uu____1833
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1897 = FStar_Options.print_universes ()  in
           if uu____1897
           then
             let uu____1898 = term_to_string t  in
             let uu____1899 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1898 uu____1899
           else term_to_string t
       | FStar_Syntax_Syntax.Tm_unknown  -> "_")

and (pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string) =
  fun x  ->
    let uu____1902 =
      let uu____1903 = FStar_Options.ugly ()  in Prims.op_Negation uu____1903
       in
    if uu____1902
    then
      let e =
        let uu____1905 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Syntax_Resugar.resugar_pat x uu____1905  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1928 = fv_to_string l  in
           let uu____1929 =
             let uu____1930 =
               FStar_List.map
                 (fun uu____1941  ->
                    match uu____1941 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1930 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1928 uu____1929
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1953) ->
           let uu____1958 = FStar_Options.print_bound_var_types ()  in
           if uu____1958
           then
             let uu____1959 = bv_to_string x1  in
             let uu____1960 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1959 uu____1960
           else
             (let uu____1962 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1962)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1964 = FStar_Options.print_bound_var_types ()  in
           if uu____1964
           then
             let uu____1965 = bv_to_string x1  in
             let uu____1966 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1965 uu____1966
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1970 = FStar_Options.print_real_names ()  in
           if uu____1970
           then
             let uu____1971 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1971
           else "_")

and (lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun quals  ->
    fun lbs  ->
      let uu____1983 = quals_to_string' quals  in
      let uu____1984 =
        let uu____1985 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____2001 =
                    attrs_to_string lb.FStar_Syntax_Syntax.lbattrs  in
                  let uu____2002 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____2003 =
                    let uu____2004 = FStar_Options.print_universes ()  in
                    if uu____2004
                    then
                      let uu____2005 =
                        let uu____2006 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____2006 ">"  in
                      Prims.strcat "<" uu____2005
                    else ""  in
                  let uu____2008 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____2009 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format5 "%s%s %s : %s = %s" uu____2001
                    uu____2002 uu____2003 uu____2008 uu____2009))
           in
        FStar_Util.concat_l "\n and " uu____1985  in
      FStar_Util.format3 "%slet %s %s" uu____1983
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1984

and (attrs_to_string :
  FStar_Syntax_Syntax.attribute Prims.list -> Prims.string) =
  fun uu___73_2015  ->
    match uu___73_2015 with
    | [] -> ""
    | tms ->
        let uu____2021 =
          let uu____2022 =
            FStar_List.map
              (fun t  ->
                 let uu____2028 = term_to_string t  in paren uu____2028) tms
             in
          FStar_All.pipe_right uu____2022 (FStar_String.concat "; ")  in
        FStar_Util.format1 "[@ %s]" uu____2021

and (lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string) =
  fun lc  ->
    let uu____2032 = FStar_Options.print_effect_args ()  in
    if uu____2032
    then
      let uu____2033 = FStar_Syntax_Syntax.lcomp_comp lc  in
      comp_to_string uu____2033
    else
      (let uu____2035 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____2036 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____2035 uu____2036)

and (aqual_to_string : FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun uu___74_2037  ->
    match uu___74_2037 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false )) ->
        "#"
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true )) ->
        "#."
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> "$"
    | uu____2038 -> ""

and (imp_to_string :
  Prims.string -> FStar_Syntax_Syntax.aqual -> Prims.string) =
  fun s  ->
    fun aq  ->
      let uu____2041 = aqual_to_string aq  in Prims.strcat uu____2041 s

and (binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string) =
  fun is_arrow  ->
    fun b  ->
      let uu____2044 =
        let uu____2045 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____2045  in
      if uu____2044
      then
        let uu____2046 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____2046 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____2052 = b  in
         match uu____2052 with
         | (a,imp) ->
             let uu____2055 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____2055
             then
               let uu____2056 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____2056
             else
               (let uu____2058 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____2060 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____2060)
                   in
                if uu____2058
                then
                  let uu____2061 = nm_to_string a  in
                  imp_to_string uu____2061 imp
                else
                  (let uu____2063 =
                     let uu____2064 = nm_to_string a  in
                     let uu____2065 =
                       let uu____2066 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____2066  in
                     Prims.strcat uu____2064 uu____2065  in
                   imp_to_string uu____2063 imp)))

and (binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' false b

and (arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string) =
  fun b  -> binder_to_string' true b

and (binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string) =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____2072 = FStar_Options.print_implicits ()  in
        if uu____2072 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____2074 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____2074 (FStar_String.concat sep)
      else
        (let uu____2082 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____2082 (FStar_String.concat sep))

and (arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
    FStar_Pervasives_Native.tuple2 -> Prims.string)
  =
  fun uu___75_2089  ->
    match uu___75_2089 with
    | (a,imp) ->
        let uu____2096 = term_to_string a  in imp_to_string uu____2096 imp

and (args_to_string : FStar_Syntax_Syntax.args -> Prims.string) =
  fun args  ->
    let args1 =
      let uu____2099 = FStar_Options.print_implicits ()  in
      if uu____2099 then args else filter_imp args  in
    let uu____2103 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____2103 (FStar_String.concat " ")

and (comp_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let uu____2116 = FStar_Options.ugly ()  in
      if uu____2116
      then comp_to_string c
      else
        (let e = FStar_Syntax_Resugar.resugar_comp' env c  in
         let d = FStar_Parser_ToDocument.term_to_document e  in
         FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
           (Prims.parse_int "100") d)

and (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c  ->
    let uu____2121 =
      let uu____2122 = FStar_Options.ugly ()  in Prims.op_Negation uu____2122
       in
    if uu____2121
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2136 =
             let uu____2137 = FStar_Syntax_Subst.compress t  in
             uu____2137.FStar_Syntax_Syntax.n  in
           (match uu____2136 with
            | FStar_Syntax_Syntax.Tm_type uu____2140 when
                let uu____2141 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2141 -> term_to_string t
            | uu____2142 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2144 = univ_to_string u  in
                     let uu____2145 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____2144 uu____2145
                 | uu____2146 ->
                     let uu____2149 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____2149))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2160 =
             let uu____2161 = FStar_Syntax_Subst.compress t  in
             uu____2161.FStar_Syntax_Syntax.n  in
           (match uu____2160 with
            | FStar_Syntax_Syntax.Tm_type uu____2164 when
                let uu____2165 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____2165 -> term_to_string t
            | uu____2166 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2168 = univ_to_string u  in
                     let uu____2169 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____2168 uu____2169
                 | uu____2170 ->
                     let uu____2173 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____2173))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2176 = FStar_Options.print_effect_args ()  in
             if uu____2176
             then
               let uu____2177 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____2178 =
                 let uu____2179 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____2179 (FStar_String.concat ", ")
                  in
               let uu____2186 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____2187 =
                 let uu____2188 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____2188 (FStar_String.concat ", ")
                  in
               let uu____2207 =
                 let uu____2208 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____2208 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2177
                 uu____2178 uu____2186 uu____2187 uu____2207
             else
               (let uu____2218 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___76_2222  ->
                           match uu___76_2222 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2223 -> false)))
                    &&
                    (let uu____2225 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____2225)
                   in
                if uu____2218
                then
                  let uu____2226 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____2226
                else
                  (let uu____2228 =
                     ((let uu____2231 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____2231) &&
                        (let uu____2233 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____2233))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____2228
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2235 =
                        (let uu____2238 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____2238) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___77_2242  ->
                                   match uu___77_2242 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2243 -> false)))
                         in
                      if uu____2235
                      then
                        let uu____2244 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____2244
                      else
                        (let uu____2246 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____2247 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____2246 uu____2247))))
              in
           let dec =
             let uu____2249 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___78_2259  ->
                       match uu___78_2259 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2265 =
                             let uu____2266 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2266
                              in
                           [uu____2265]
                       | uu____2267 -> []))
                in
             FStar_All.pipe_right uu____2249 (FStar_String.concat " ")  in
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
    | FStar_Syntax_Syntax.DECREASES uu____2271 -> ""

and (formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string) =
  fun phi  -> term_to_string phi

and (metadata_to_string : FStar_Syntax_Syntax.metadata -> Prims.string) =
  fun uu___79_2277  ->
    match uu___79_2277 with
    | FStar_Syntax_Syntax.Meta_pattern ps ->
        let pats =
          let uu____2290 =
            FStar_All.pipe_right ps
              (FStar_List.map
                 (fun args  ->
                    let uu____2320 =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____2338  ->
                              match uu____2338 with
                              | (t,uu____2344) -> term_to_string t))
                       in
                    FStar_All.pipe_right uu____2320
                      (FStar_String.concat "; ")))
             in
          FStar_All.pipe_right uu____2290 (FStar_String.concat "\\/")  in
        FStar_Util.format1 "{Meta_pattern %s}" pats
    | FStar_Syntax_Syntax.Meta_named lid ->
        let uu____2350 = sli lid  in
        FStar_Util.format1 "{Meta_named %s}" uu____2350
    | FStar_Syntax_Syntax.Meta_labeled (l,r,uu____2353) ->
        let uu____2354 = FStar_Range.string_of_range r  in
        FStar_Util.format2 "{Meta_labeled (%s, %s)}" l uu____2354
    | FStar_Syntax_Syntax.Meta_desugared msi -> "{Meta_desugared}"
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____2362 = sli m  in
        let uu____2363 = term_to_string t  in
        FStar_Util.format2 "{Meta_monadic(%s @ %s)}" uu____2362 uu____2363
    | FStar_Syntax_Syntax.Meta_monadic_lift (m,m',t) ->
        let uu____2371 = sli m  in
        let uu____2372 = sli m'  in
        let uu____2373 = term_to_string t  in
        FStar_Util.format3 "{Meta_monadic_lift(%s -> %s @ %s)}" uu____2371
          uu____2372 uu____2373

let (term_to_string' :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun x  ->
      let uu____2384 = FStar_Options.ugly ()  in
      if uu____2384
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
      let uu____2398 = b  in
      match uu____2398 with
      | (a,imp) ->
          let n1 =
            let uu____2402 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____2402
            then FStar_Util.JsonNull
            else
              (let uu____2404 =
                 let uu____2405 = nm_to_string a  in
                 imp_to_string uu____2405 imp  in
               FStar_Util.JsonStr uu____2404)
             in
          let t =
            let uu____2407 = term_to_string' env a.FStar_Syntax_Syntax.sort
               in
            FStar_Util.JsonStr uu____2407  in
          FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let (binders_to_json :
  FStar_Syntax_DsEnv.env -> FStar_Syntax_Syntax.binders -> FStar_Util.json) =
  fun env  ->
    fun bs  ->
      let uu____2430 = FStar_List.map (binder_to_json env) bs  in
      FStar_Util.JsonList uu____2430
  
let (enclose_universes : Prims.string -> Prims.string) =
  fun s  ->
    let uu____2438 = FStar_Options.print_universes ()  in
    if uu____2438 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let (tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string) =
  fun s  ->
    let uu____2445 =
      let uu____2446 = FStar_Options.ugly ()  in Prims.op_Negation uu____2446
       in
    if uu____2445
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2450 = s  in
       match uu____2450 with
       | (us,t) ->
           let uu____2457 =
             let uu____2458 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2458  in
           let uu____2459 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2457 uu____2459)
  
let (action_to_string : FStar_Syntax_Syntax.action -> Prims.string) =
  fun a  ->
    let uu____2465 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2466 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2467 =
      let uu____2468 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2468  in
    let uu____2469 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2470 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2465 uu____2466 uu____2467
      uu____2469 uu____2470
  
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
          let uu____2495 =
            let uu____2496 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2496  in
          if uu____2495
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2509 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2509 (FStar_String.concat ",\n\t")
                in
             let uu____2518 =
               let uu____2521 =
                 let uu____2524 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2525 =
                   let uu____2528 =
                     let uu____2529 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2529  in
                   let uu____2530 =
                     let uu____2533 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2534 =
                       let uu____2537 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2538 =
                         let uu____2541 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2542 =
                           let uu____2545 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2546 =
                             let uu____2549 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2550 =
                               let uu____2553 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2554 =
                                 let uu____2557 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2558 =
                                   let uu____2561 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2562 =
                                     let uu____2565 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2566 =
                                       let uu____2569 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2570 =
                                         let uu____2573 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2574 =
                                           let uu____2577 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2578 =
                                             let uu____2581 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2582 =
                                               let uu____2585 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2586 =
                                                 let uu____2589 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2590 =
                                                   let uu____2593 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2593]  in
                                                 uu____2589 :: uu____2590  in
                                               uu____2585 :: uu____2586  in
                                             uu____2581 :: uu____2582  in
                                           uu____2577 :: uu____2578  in
                                         uu____2573 :: uu____2574  in
                                       uu____2569 :: uu____2570  in
                                     uu____2565 :: uu____2566  in
                                   uu____2561 :: uu____2562  in
                                 uu____2557 :: uu____2558  in
                               uu____2553 :: uu____2554  in
                             uu____2549 :: uu____2550  in
                           uu____2545 :: uu____2546  in
                         uu____2541 :: uu____2542  in
                       uu____2537 :: uu____2538  in
                     uu____2533 :: uu____2534  in
                   uu____2528 :: uu____2530  in
                 uu____2524 :: uu____2525  in
               (if for_free then "_for_free " else "") :: uu____2521  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2518)
  
let (eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string) =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun x  ->
    let uu____2610 =
      let uu____2611 = FStar_Options.ugly ()  in Prims.op_Negation uu____2611
       in
    if uu____2610
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2617 -> ""
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
             (lid,univs1,tps,k,uu____2628,uu____2629) ->
             let quals_str = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let binders_str = binders_to_string " " tps  in
             let term_str = term_to_string k  in
             let uu____2641 = FStar_Options.print_universes ()  in
             if uu____2641
             then
               let uu____2642 = univ_names_to_string univs1  in
               FStar_Util.format5 "%stype %s<%s> %s : %s" quals_str
                 lid.FStar_Ident.str uu____2642 binders_str term_str
             else
               FStar_Util.format4 "%stype %s %s : %s" quals_str
                 lid.FStar_Ident.str binders_str term_str
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2647,uu____2648,uu____2649) ->
             let uu____2654 = FStar_Options.print_universes ()  in
             if uu____2654
             then
               let uu____2655 = univ_names_to_string univs1  in
               let uu____2656 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2655
                 lid.FStar_Ident.str uu____2656
             else
               (let uu____2658 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2658)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2662 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2663 =
               let uu____2664 = FStar_Options.print_universes ()  in
               if uu____2664
               then
                 let uu____2665 = univ_names_to_string univs1  in
                 FStar_Util.format1 "<%s>" uu____2665
               else ""  in
             let uu____2667 = term_to_string t  in
             FStar_Util.format4 "%sval %s %s : %s" uu____2662
               lid.FStar_Ident.str uu____2663 uu____2667
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2669,f) ->
             let uu____2671 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2671
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2673) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2679 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2679
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2681) ->
             let uu____2690 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2690 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2708) -> lift_wp
               | (uu____2715,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2723 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2723 with
              | (us,t) ->
                  let uu____2734 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2735 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2736 = univ_names_to_string us  in
                  let uu____2737 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2734 uu____2735 uu____2736 uu____2737)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2747 = FStar_Options.print_universes ()  in
             if uu____2747
             then
               let uu____2748 =
                 let uu____2753 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2753  in
               (match uu____2748 with
                | (univs2,t) ->
                    let uu____2756 =
                      let uu____2769 =
                        let uu____2770 = FStar_Syntax_Subst.compress t  in
                        uu____2770.FStar_Syntax_Syntax.n  in
                      match uu____2769 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2811 -> failwith "impossible"  in
                    (match uu____2756 with
                     | (tps1,c1) ->
                         let uu____2842 = sli l  in
                         let uu____2843 = univ_names_to_string univs2  in
                         let uu____2844 = binders_to_string " " tps1  in
                         let uu____2845 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2842 uu____2843 uu____2844 uu____2845))
             else
               (let uu____2847 = sli l  in
                let uu____2848 = binders_to_string " " tps  in
                let uu____2849 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2847 uu____2848
                  uu____2849)
         | FStar_Syntax_Syntax.Sig_splice (lids,t) ->
             let uu____2856 =
               let uu____2857 = FStar_List.map FStar_Ident.string_of_lid lids
                  in
               FStar_All.pipe_left (FStar_String.concat "; ") uu____2857  in
             let uu____2862 = term_to_string t  in
             FStar_Util.format2 "splice[%s] (%s)" uu____2856 uu____2862
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2863 ->
           let uu____2866 = attrs_to_string x.FStar_Syntax_Syntax.sigattrs
              in
           Prims.strcat uu____2866 (Prims.strcat "\n" basic))
  
let (format_error : FStar_Range.range -> Prims.string -> Prims.string) =
  fun r  ->
    fun msg  ->
      let uu____2877 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2877 msg
  
let rec (sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2883,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2885;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2887;
                       FStar_Syntax_Syntax.lbdef = uu____2888;
                       FStar_Syntax_Syntax.lbattrs = uu____2889;
                       FStar_Syntax_Syntax.lbpos = uu____2890;_}::[]),uu____2891)
        ->
        let uu____2918 = lbname_to_string lb  in
        let uu____2919 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2918 uu____2919
    | uu____2920 ->
        let uu____2921 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2921 (FStar_String.concat ", ")
  
let rec (modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string) =
  fun m  ->
    let uu____2937 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2938 =
      let uu____2939 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2939 (FStar_String.concat "\n")  in
    let uu____2944 =
      let uu____2945 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.exports  in
      FStar_All.pipe_right uu____2945 (FStar_String.concat "\n")  in
    FStar_Util.format3 "module %s\nDeclarations:\n%s\nExports:\n%s\n"
      uu____2937 uu____2938 uu____2944
  
let (subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string) =
  fun uu___80_2954  ->
    match uu___80_2954 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2957 = FStar_Util.string_of_int i  in
        let uu____2958 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2957 uu____2958
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2961 = bv_to_string x  in
        let uu____2962 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2961 uu____2962
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2969 = bv_to_string x  in
        let uu____2970 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2969 uu____2970
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2973 = FStar_Util.string_of_int i  in
        let uu____2974 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2973 uu____2974
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2977 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2977
  
let (subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string) =
  fun s  ->
    let uu____2983 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2983 (FStar_String.concat "; ")
  
let (abs_ascription_to_string :
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
    FStar_Pervasives_Native.option -> Prims.string)
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder ()  in
    let uu____3008 =
      match ascription with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.string_builder_append strb "None"
      | FStar_Pervasives_Native.Some (FStar_Util.Inl lc) ->
          let uu____3018 = FStar_Util.string_builder_append strb "Some Inr "
             in
          let uu____3019 =
            FStar_Ident.text_of_lid lc.FStar_Syntax_Syntax.eff_name  in
          FStar_Util.string_builder_append strb uu____3019
      | FStar_Pervasives_Native.Some (FStar_Util.Inr lid) ->
          let uu____3025 = FStar_Util.string_builder_append strb "Some Inr "
             in
          let uu____3026 = FStar_Ident.text_of_lid lid  in
          FStar_Util.string_builder_append strb uu____3026
       in
    FStar_Util.string_of_string_builder strb
  
let list_to_string :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          let uu____3058 = FStar_Util.string_builder_append strb "["  in
          let uu____3059 =
            let uu____3060 = f x  in
            FStar_Util.string_builder_append strb uu____3060  in
          let uu____3061 =
            FStar_List.iter
              (fun x1  ->
                 let uu____3066 = FStar_Util.string_builder_append strb "; "
                    in
                 let uu____3067 = f x1  in
                 FStar_Util.string_builder_append strb uu____3067) xs
             in
          let uu____3068 = FStar_Util.string_builder_append strb "]"  in
          FStar_Util.string_of_string_builder strb
  
let set_to_string :
  'a . ('a -> Prims.string) -> 'a FStar_Util.set -> Prims.string =
  fun f  ->
    fun s  ->
      let elts = FStar_Util.set_elements s  in
      match elts with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Util.new_string_builder ()  in
          let uu____3103 = FStar_Util.string_builder_append strb "{"  in
          let uu____3104 =
            let uu____3105 = f x  in
            FStar_Util.string_builder_append strb uu____3105  in
          let uu____3106 =
            FStar_List.iter
              (fun x1  ->
                 let uu____3111 = FStar_Util.string_builder_append strb ", "
                    in
                 let uu____3112 = f x1  in
                 FStar_Util.string_builder_append strb uu____3112) xs
             in
          let uu____3113 = FStar_Util.string_builder_append strb "}"  in
          FStar_Util.string_of_string_builder strb
  
let (bvs_to_string :
  Prims.string -> FStar_Syntax_Syntax.bv Prims.list -> Prims.string) =
  fun sep  ->
    fun bvs  ->
      let uu____3128 = FStar_List.map FStar_Syntax_Syntax.mk_binder bvs  in
      binders_to_string sep uu____3128
  