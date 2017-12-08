open Prims
let rec delta_depth_to_string :
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___116_3  ->
    match uu___116_3 with
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
    ('Auu____233,'Auu____232) FStar_Util.either -> Prims.bool
  =
  fun uu___117_241  ->
    match uu___117_241 with
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
         (fun uu___118_304  ->
            match uu___118_304 with
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
  fun uu___119_567  ->
    match uu___119_567 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let tag_of_term : FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____574 = db_to_string x  in Prims.strcat "Tm_bvar: " uu____574
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____576 = nm_to_string x  in Prims.strcat "Tm_name: " uu____576
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____578 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        Prims.strcat "Tm_fvar: " uu____578
    | FStar_Syntax_Syntax.Tm_uinst uu____579 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____586 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____587 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____588 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____605 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____618 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____625 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____640 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____663 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____690 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____703 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____720,m) ->
        let uu____762 = FStar_ST.op_Bang m  in
        (match uu____762 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____839 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____844 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
  
let uvar_to_string : FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____854 = FStar_Options.hide_uvar_nums ()  in
    if uu____854
    then "?"
    else
      (let uu____856 =
         let uu____857 = FStar_Syntax_Unionfind.uvar_id u  in
         FStar_All.pipe_right uu____857 FStar_Util.string_of_int  in
       Prims.strcat "?" uu____856)
  
let version_to_string : FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____861 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major  in
    let uu____862 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor  in
    FStar_Util.format2 "%s.%s" uu____861 uu____862
  
let univ_uvar_to_string : FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____866 = FStar_Options.hide_uvar_nums ()  in
    if uu____866
    then "?"
    else
      (let uu____868 =
         let uu____869 =
           let uu____870 = FStar_Syntax_Unionfind.univ_uvar_id u  in
           FStar_All.pipe_right uu____870 FStar_Util.string_of_int  in
         let uu____871 =
           let uu____872 = version_to_string (FStar_Pervasives_Native.snd u)
              in
           Prims.strcat ":" uu____872  in
         Prims.strcat uu____869 uu____871  in
       Prims.strcat "?" uu____868)
  
let rec int_of_univ :
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____889 = FStar_Syntax_Subst.compress_univ u  in
      match uu____889 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____899 -> (n1, (FStar_Pervasives_Native.Some u))
  
let rec univ_to_string : FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____905 =
      let uu____906 = FStar_Options.ugly ()  in Prims.op_Negation uu____906
       in
    if uu____905
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange
         in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____910 = FStar_Syntax_Subst.compress_univ u  in
       match uu____910 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____922 = FStar_Util.string_of_int x  in
           Prims.strcat "@" uu____922
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____924 = int_of_univ (Prims.parse_int "1") u1  in
           (match uu____924 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____938 = univ_to_string u2  in
                let uu____939 = FStar_Util.string_of_int n1  in
                FStar_Util.format2 "(%s + %s)" uu____938 uu____939)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____943 =
             let uu____944 = FStar_List.map univ_to_string us  in
             FStar_All.pipe_right uu____944 (FStar_String.concat ", ")  in
           FStar_Util.format1 "(max %s)" uu____943
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
  
let univs_to_string : FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____956 = FStar_List.map univ_to_string us  in
    FStar_All.pipe_right uu____956 (FStar_String.concat ", ")
  
let univ_names_to_string : FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____968 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us  in
    FStar_All.pipe_right uu____968 (FStar_String.concat ", ")
  
let qual_to_string : FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___120_977  ->
    match uu___120_977 with
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
        let uu____979 = lid_to_string l  in
        FStar_Util.format1 "(Discriminator %s)" uu____979
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____982 = lid_to_string l  in
        FStar_Util.format2 "(Projector %s %s)" uu____982 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____993 =
          let uu____994 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____994  in
        let uu____997 =
          let uu____998 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____998 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordType %s %s)" uu____993 uu____997
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1017 =
          let uu____1018 = FStar_Ident.path_of_ns ns  in
          FStar_Ident.text_of_path uu____1018  in
        let uu____1021 =
          let uu____1022 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id)
             in
          FStar_All.pipe_right uu____1022 (FStar_String.concat ", ")  in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1017 uu____1021
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1032 = lid_to_string eff_lid  in
        FStar_Util.format1 "(Action %s)" uu____1032
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
    | uu____1041 ->
        let uu____1044 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string)  in
        FStar_All.pipe_right uu____1044 (FStar_String.concat " ")
  
let quals_to_string' :
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1060 ->
        let uu____1063 = quals_to_string quals  in
        Prims.strcat uu____1063 " "
  
let rec term_to_string : FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1119 =
      let uu____1120 = FStar_Options.ugly ()  in Prims.op_Negation uu____1120
       in
    if uu____1119
    then
      let e = FStar_Syntax_Resugar.resugar_term x  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x  in
       let x2 =
         let uu____1126 = FStar_Options.print_implicits ()  in
         if uu____1126 then x1 else FStar_Syntax_Util.unmeta x1  in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1128 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1153,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1189 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1219 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1237  ->
                                 match uu____1237 with
                                 | (t1,uu____1243) -> term_to_string t1))
                          in
                       FStar_All.pipe_right uu____1219
                         (FStar_String.concat "; ")))
                in
             FStar_All.pipe_right uu____1189 (FStar_String.concat "\\/")  in
           let uu____1248 = term_to_string t  in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1248
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1260 = tag_of_term t  in
           let uu____1261 = sli m  in
           let uu____1262 = term_to_string t'  in
           let uu____1263 = term_to_string t  in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1260 uu____1261
             uu____1262 uu____1263
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1276 = tag_of_term t  in
           let uu____1277 = term_to_string t'  in
           let uu____1278 = sli m0  in
           let uu____1279 = sli m1  in
           let uu____1280 = term_to_string t  in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1276
             uu____1277 uu____1278 uu____1279 uu____1280
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1282,s,uu____1284)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1301 = FStar_Range.string_of_range r  in
           let uu____1302 = term_to_string t  in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1301
             uu____1302
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1309 = lid_to_string l  in
           let uu____1310 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
           let uu____1311 = term_to_string t  in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1309 uu____1310
             uu____1311
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1313) ->
           let uu____1318 = term_to_string t  in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1318
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1320 = db_to_string x3  in
           let uu____1321 =
             let uu____1322 =
               let uu____1323 = tag_of_term x3.FStar_Syntax_Syntax.sort  in
               Prims.strcat uu____1323 ")"  in
             Prims.strcat ":(" uu____1322  in
           Prims.strcat uu____1320 uu____1321
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1327) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1354 = FStar_Options.print_universes ()  in
           if uu____1354
           then
             let uu____1355 = univ_to_string u  in
             FStar_Util.format1 "Type u#(%s)" uu____1355
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1375 = binders_to_string " -> " bs  in
           let uu____1376 = comp_to_string c  in
           FStar_Util.format2 "(%s -> %s)" uu____1375 uu____1376
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1401 = binders_to_string " " bs  in
                let uu____1402 = term_to_string t2  in
                let uu____1403 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1407 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ
                        in
                     term_to_string uu____1407)
                   in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1401 uu____1402
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1403
            | uu____1410 ->
                let uu____1413 = binders_to_string " " bs  in
                let uu____1414 = term_to_string t2  in
                FStar_Util.format2 "(fun %s -> %s)" uu____1413 uu____1414)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1421 = bv_to_string xt  in
           let uu____1422 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string
              in
           let uu____1425 = FStar_All.pipe_right f formula_to_string  in
           FStar_Util.format3 "(%s:%s{%s})" uu____1421 uu____1422 uu____1425
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1450 = term_to_string t  in
           let uu____1451 = args_to_string args  in
           FStar_Util.format2 "(%s %s)" uu____1450 uu____1451
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1470 = lbs_to_string [] lbs  in
           let uu____1471 = term_to_string e  in
           FStar_Util.format2 "%s\nin\n%s" uu____1470 uu____1471
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1532 =
                   let uu____1533 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid  in
                   FStar_All.pipe_right uu____1533
                     (FStar_Util.dflt "default")
                    in
                 let uu____1538 = term_to_string t  in
                 FStar_Util.format2 "[%s] %s" uu____1532 uu____1538
             | FStar_Util.Inr c -> comp_to_string c  in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1554 = term_to_string t  in
                 FStar_Util.format1 "by %s" uu____1554
              in
           let uu____1555 = term_to_string e  in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1555 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1594 = term_to_string head1  in
           let uu____1595 =
             let uu____1596 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1632  ->
                       match uu____1632 with
                       | (p,wopt,e) ->
                           let uu____1648 =
                             FStar_All.pipe_right p pat_to_string  in
                           let uu____1649 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1651 =
                                   FStar_All.pipe_right w term_to_string  in
                                 FStar_Util.format1 "when %s" uu____1651
                              in
                           let uu____1652 =
                             FStar_All.pipe_right e term_to_string  in
                           FStar_Util.format3 "%s %s -> %s" uu____1648
                             uu____1649 uu____1652))
                in
             FStar_Util.concat_l "\n\t|" uu____1596  in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1594 uu____1595
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1659 = FStar_Options.print_universes ()  in
           if uu____1659
           then
             let uu____1660 = term_to_string t  in
             let uu____1661 = univs_to_string us  in
             FStar_Util.format2 "%s<%s>" uu____1660 uu____1661
           else term_to_string t
       | uu____1663 -> tag_of_term x2)

and pat_to_string : FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1665 =
      let uu____1666 = FStar_Options.ugly ()  in Prims.op_Negation uu____1666
       in
    if uu____1665
    then
      let e = FStar_Syntax_Resugar.resugar_pat x  in
      let d = FStar_Parser_ToDocument.pat_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1688 = fv_to_string l  in
           let uu____1689 =
             let uu____1690 =
               FStar_List.map
                 (fun uu____1701  ->
                    match uu____1701 with
                    | (x1,b) ->
                        let p = pat_to_string x1  in
                        if b then Prims.strcat "#" p else p) pats
                in
             FStar_All.pipe_right uu____1690 (FStar_String.concat " ")  in
           FStar_Util.format2 "(%s %s)" uu____1688 uu____1689
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1713) ->
           let uu____1718 = FStar_Options.print_bound_var_types ()  in
           if uu____1718
           then
             let uu____1719 = bv_to_string x1  in
             let uu____1720 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 ".%s:%s" uu____1719 uu____1720
           else
             (let uu____1722 = bv_to_string x1  in
              FStar_Util.format1 ".%s" uu____1722)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1724 = FStar_Options.print_bound_var_types ()  in
           if uu____1724
           then
             let uu____1725 = bv_to_string x1  in
             let uu____1726 = term_to_string x1.FStar_Syntax_Syntax.sort  in
             FStar_Util.format2 "%s:%s" uu____1725 uu____1726
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1730 = FStar_Options.print_real_names ()  in
           if uu____1730
           then
             let uu____1731 = bv_to_string x1  in
             Prims.strcat "Pat_wild " uu____1731
           else "_")

and lbs_to_string :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1743 = quals_to_string' quals  in
      let uu____1744 =
        let uu____1745 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1760 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname  in
                  let uu____1761 =
                    let uu____1762 = FStar_Options.print_universes ()  in
                    if uu____1762
                    then
                      let uu____1763 =
                        let uu____1764 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs
                           in
                        Prims.strcat uu____1764 ">"  in
                      Prims.strcat "<" uu____1763
                    else ""  in
                  let uu____1766 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp  in
                  let uu____1767 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string
                     in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1760 uu____1761
                    uu____1766 uu____1767))
           in
        FStar_Util.concat_l "\n and " uu____1745  in
      FStar_Util.format3 "%slet %s %s" uu____1743
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1744

and lcomp_to_string : FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1774 = FStar_Options.print_effect_args ()  in
    if uu____1774
    then
      let uu____1775 = lc.FStar_Syntax_Syntax.comp ()  in
      comp_to_string uu____1775
    else
      (let uu____1777 = sli lc.FStar_Syntax_Syntax.eff_name  in
       let uu____1778 = term_to_string lc.FStar_Syntax_Syntax.res_typ  in
       FStar_Util.format2 "%s %s" uu____1777 uu____1778)

and imp_to_string :
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___121_1780  ->
      match uu___121_1780 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1783 -> s

and binder_to_string' :
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1788 =
        let uu____1789 = FStar_Options.ugly ()  in
        Prims.op_Negation uu____1789  in
      if uu____1788
      then
        let uu____1790 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange  in
        match uu____1790 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1796 = b  in
         match uu____1796 with
         | (a,imp) ->
             let uu____1799 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____1799
             then
               let uu____1800 = term_to_string a.FStar_Syntax_Syntax.sort  in
               Prims.strcat "_:" uu____1800
             else
               (let uu____1802 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1804 = FStar_Options.print_bound_var_types ()
                        in
                     Prims.op_Negation uu____1804)
                   in
                if uu____1802
                then
                  let uu____1805 = nm_to_string a  in
                  imp_to_string uu____1805 imp
                else
                  (let uu____1807 =
                     let uu____1808 = nm_to_string a  in
                     let uu____1809 =
                       let uu____1810 =
                         term_to_string a.FStar_Syntax_Syntax.sort  in
                       Prims.strcat ":" uu____1810  in
                     Prims.strcat uu____1808 uu____1809  in
                   imp_to_string uu____1807 imp)))

and binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b

and arrow_binder_to_string : FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b

and binders_to_string :
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1816 = FStar_Options.print_implicits ()  in
        if uu____1816 then bs else filter_imp bs  in
      if sep = " -> "
      then
        let uu____1818 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string)
           in
        FStar_All.pipe_right uu____1818 (FStar_String.concat sep)
      else
        (let uu____1826 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string)  in
         FStar_All.pipe_right uu____1826 (FStar_String.concat sep))

and arg_to_string :
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___122_1833  ->
    match uu___122_1833 with
    | (a,imp) ->
        let uu____1846 = term_to_string a  in imp_to_string uu____1846 imp

and args_to_string : FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1849 = FStar_Options.print_implicits ()  in
      if uu____1849 then args else filter_imp args  in
    let uu____1853 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____1853 (FStar_String.concat " ")

and comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1867 =
      let uu____1868 = FStar_Options.ugly ()  in Prims.op_Negation uu____1868
       in
    if uu____1867
    then
      let e = FStar_Syntax_Resugar.resugar_comp c  in
      let d = FStar_Parser_ToDocument.term_to_document e  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1882 =
             let uu____1883 = FStar_Syntax_Subst.compress t  in
             uu____1883.FStar_Syntax_Syntax.n  in
           (match uu____1882 with
            | FStar_Syntax_Syntax.Tm_type uu____1886 when
                let uu____1887 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1887 -> term_to_string t
            | uu____1888 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1890 = univ_to_string u  in
                     let uu____1891 = term_to_string t  in
                     FStar_Util.format2 "Tot<%s> %s" uu____1890 uu____1891
                 | uu____1892 ->
                     let uu____1895 = term_to_string t  in
                     FStar_Util.format1 "Tot %s" uu____1895))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1906 =
             let uu____1907 = FStar_Syntax_Subst.compress t  in
             uu____1907.FStar_Syntax_Syntax.n  in
           (match uu____1906 with
            | FStar_Syntax_Syntax.Tm_type uu____1910 when
                let uu____1911 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ())
                   in
                Prims.op_Negation uu____1911 -> term_to_string t
            | uu____1912 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1914 = univ_to_string u  in
                     let uu____1915 = term_to_string t  in
                     FStar_Util.format2 "GTot<%s> %s" uu____1914 uu____1915
                 | uu____1916 ->
                     let uu____1919 = term_to_string t  in
                     FStar_Util.format1 "GTot %s" uu____1919))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1922 = FStar_Options.print_effect_args ()  in
             if uu____1922
             then
               let uu____1923 = sli c1.FStar_Syntax_Syntax.effect_name  in
               let uu____1924 =
                 let uu____1925 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string)
                    in
                 FStar_All.pipe_right uu____1925 (FStar_String.concat ", ")
                  in
               let uu____1932 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ  in
               let uu____1933 =
                 let uu____1934 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string)
                    in
                 FStar_All.pipe_right uu____1934 (FStar_String.concat ", ")
                  in
               let uu____1955 =
                 let uu____1956 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string)
                    in
                 FStar_All.pipe_right uu____1956 (FStar_String.concat " ")
                  in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1923
                 uu____1924 uu____1932 uu____1933 uu____1955
             else
               (let uu____1966 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___123_1970  ->
                           match uu___123_1970 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1971 -> false)))
                    &&
                    (let uu____1973 = FStar_Options.print_effect_args ()  in
                     Prims.op_Negation uu____1973)
                   in
                if uu____1966
                then
                  let uu____1974 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ  in
                  FStar_Util.format1 "Tot %s" uu____1974
                else
                  (let uu____1976 =
                     ((let uu____1979 = FStar_Options.print_effect_args ()
                          in
                       Prims.op_Negation uu____1979) &&
                        (let uu____1981 = FStar_Options.print_implicits ()
                            in
                         Prims.op_Negation uu____1981))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid)
                      in
                   if uu____1976
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1983 =
                        (let uu____1986 = FStar_Options.print_effect_args ()
                            in
                         Prims.op_Negation uu____1986) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___124_1990  ->
                                   match uu___124_1990 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1991 -> false)))
                         in
                      if uu____1983
                      then
                        let uu____1992 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ
                           in
                        FStar_Util.format1 "ALL %s" uu____1992
                      else
                        (let uu____1994 =
                           sli c1.FStar_Syntax_Syntax.effect_name  in
                         let uu____1995 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ
                            in
                         FStar_Util.format2 "%s (%s)" uu____1994 uu____1995))))
              in
           let dec =
             let uu____1997 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___125_2007  ->
                       match uu___125_2007 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2013 =
                             let uu____2014 = term_to_string e  in
                             FStar_Util.format1 " (decreases %s)" uu____2014
                              in
                           [uu____2013]
                       | uu____2015 -> []))
                in
             FStar_All.pipe_right uu____1997 (FStar_String.concat " ")  in
           FStar_Util.format2 "%s%s" basic dec)

and cflags_to_string : FStar_Syntax_Syntax.cflags -> Prims.string =
  fun c  ->
    match c with
    | FStar_Syntax_Syntax.TOTAL  -> "total"
    | FStar_Syntax_Syntax.MLEFFECT  -> "ml"
    | FStar_Syntax_Syntax.RETURN  -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN  -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL  -> "sometrivial"
    | FStar_Syntax_Syntax.LEMMA  -> "lemma"
    | FStar_Syntax_Syntax.CPS  -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____2019 -> ""

and formula_to_string :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi

let binder_to_json : FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2028 = b  in
    match uu____2028 with
    | (a,imp) ->
        let n1 =
          let uu____2032 = FStar_Syntax_Syntax.is_null_binder b  in
          if uu____2032
          then FStar_Util.JsonNull
          else
            (let uu____2034 =
               let uu____2035 = nm_to_string a  in
               imp_to_string uu____2035 imp  in
             FStar_Util.JsonStr uu____2034)
           in
        let t =
          let uu____2037 = term_to_string a.FStar_Syntax_Syntax.sort  in
          FStar_Util.JsonStr uu____2037  in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
  
let binders_to_json : FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2053 = FStar_List.map binder_to_json bs  in
    FStar_Util.JsonList uu____2053
  
let enclose_universes : Prims.string -> Prims.string =
  fun s  ->
    let uu____2059 = FStar_Options.print_universes ()  in
    if uu____2059 then Prims.strcat "<" (Prims.strcat s ">") else ""
  
let tscheme_to_string : FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2064 =
      let uu____2065 = FStar_Options.ugly ()  in Prims.op_Negation uu____2065
       in
    if uu____2064
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s  in
      let d1 = FStar_Parser_ToDocument.decl_to_document d  in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2069 = s  in
       match uu____2069 with
       | (us,t) ->
           let uu____2076 =
             let uu____2077 = univ_names_to_string us  in
             FStar_All.pipe_left enclose_universes uu____2077  in
           let uu____2078 = term_to_string t  in
           FStar_Util.format2 "%s%s" uu____2076 uu____2078)
  
let action_to_string : FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2082 = sli a.FStar_Syntax_Syntax.action_name  in
    let uu____2083 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params  in
    let uu____2084 =
      let uu____2085 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs  in
      FStar_All.pipe_left enclose_universes uu____2085  in
    let uu____2086 = term_to_string a.FStar_Syntax_Syntax.action_typ  in
    let uu____2087 = term_to_string a.FStar_Syntax_Syntax.action_defn  in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2082 uu____2083 uu____2084
      uu____2086 uu____2087
  
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
          let uu____2104 =
            let uu____2105 = FStar_Options.ugly ()  in
            Prims.op_Negation uu____2105  in
          if uu____2104
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed  in
            let d1 = FStar_Parser_ToDocument.decl_to_document d  in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2117 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string)
                  in
               FStar_All.pipe_right uu____2117 (FStar_String.concat ",\n\t")
                in
             let uu____2126 =
               let uu____2129 =
                 let uu____2132 = lid_to_string ed.FStar_Syntax_Syntax.mname
                    in
                 let uu____2133 =
                   let uu____2136 =
                     let uu____2137 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs  in
                     FStar_All.pipe_left enclose_universes uu____2137  in
                   let uu____2138 =
                     let uu____2141 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders
                        in
                     let uu____2142 =
                       let uu____2145 =
                         term_to_string ed.FStar_Syntax_Syntax.signature  in
                       let uu____2146 =
                         let uu____2149 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____2150 =
                           let uu____2153 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp
                              in
                           let uu____2154 =
                             let uu____2157 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else
                                in
                             let uu____2158 =
                               let uu____2161 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp
                                  in
                               let uu____2162 =
                                 let uu____2165 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger
                                    in
                                 let uu____2166 =
                                   let uu____2169 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp
                                      in
                                   let uu____2170 =
                                     let uu____2173 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p
                                        in
                                     let uu____2174 =
                                       let uu____2177 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p
                                          in
                                       let uu____2178 =
                                         let uu____2181 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp
                                            in
                                         let uu____2182 =
                                           let uu____2185 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____2186 =
                                             let uu____2189 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr
                                                in
                                             let uu____2190 =
                                               let uu____2193 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr
                                                  in
                                               let uu____2194 =
                                                 let uu____2197 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr
                                                    in
                                                 let uu____2198 =
                                                   let uu____2201 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions
                                                      in
                                                   [uu____2201]  in
                                                 uu____2197 :: uu____2198  in
                                               uu____2193 :: uu____2194  in
                                             uu____2189 :: uu____2190  in
                                           uu____2185 :: uu____2186  in
                                         uu____2181 :: uu____2182  in
                                       uu____2177 :: uu____2178  in
                                     uu____2173 :: uu____2174  in
                                   uu____2169 :: uu____2170  in
                                 uu____2165 :: uu____2166  in
                               uu____2161 :: uu____2162  in
                             uu____2157 :: uu____2158  in
                           uu____2153 :: uu____2154  in
                         uu____2149 :: uu____2150  in
                       uu____2145 :: uu____2146  in
                     uu____2141 :: uu____2142  in
                   uu____2136 :: uu____2138  in
                 uu____2132 :: uu____2133  in
               (if for_free then "_for_free " else "") :: uu____2129  in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2126)
  
let eff_decl_to_string :
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
  
let rec sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2212 =
      let uu____2213 = FStar_Options.ugly ()  in Prims.op_Negation uu____2213
       in
    if uu____2212
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x  in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d  in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2219 -> ""
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
             (lid,univs1,tps,k,uu____2230,uu____2231) ->
             let uu____2240 = quals_to_string' x.FStar_Syntax_Syntax.sigquals
                in
             let uu____2241 = binders_to_string " " tps  in
             let uu____2242 = term_to_string k  in
             FStar_Util.format4 "%stype %s %s : %s" uu____2240
               lid.FStar_Ident.str uu____2241 uu____2242
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2246,uu____2247,uu____2248) ->
             let uu____2253 = FStar_Options.print_universes ()  in
             if uu____2253
             then
               let uu____2254 = univ_names_to_string univs1  in
               let uu____2255 = term_to_string t  in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2254
                 lid.FStar_Ident.str uu____2255
             else
               (let uu____2257 = term_to_string t  in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2257)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2261 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
             (match uu____2261 with
              | (univs2,t1) ->
                  let uu____2268 =
                    quals_to_string' x.FStar_Syntax_Syntax.sigquals  in
                  let uu____2269 =
                    let uu____2270 = FStar_Options.print_universes ()  in
                    if uu____2270
                    then
                      let uu____2271 = univ_names_to_string univs2  in
                      FStar_Util.format1 "<%s>" uu____2271
                    else ""  in
                  let uu____2273 = term_to_string t1  in
                  FStar_Util.format4 "%sval %s %s : %s" uu____2268
                    lid.FStar_Ident.str uu____2269 uu____2273)
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2275,f) ->
             let uu____2277 = term_to_string f  in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2277
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2279) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2285 = term_to_string e  in
             FStar_Util.format1 "let _ = %s" uu____2285
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2287) ->
             let uu____2296 = FStar_List.map sigelt_to_string ses  in
             FStar_All.pipe_right uu____2296 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2314) -> lift_wp
               | (uu____2321,FStar_Pervasives_Native.Some lift) -> lift  in
             let uu____2329 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp)
                in
             (match uu____2329 with
              | (us,t) ->
                  let uu____2340 =
                    lid_to_string se.FStar_Syntax_Syntax.source  in
                  let uu____2341 =
                    lid_to_string se.FStar_Syntax_Syntax.target  in
                  let uu____2342 = univ_names_to_string us  in
                  let uu____2343 = term_to_string t  in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2340 uu____2341 uu____2342 uu____2343)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
             let uu____2353 = FStar_Options.print_universes ()  in
             if uu____2353
             then
               let uu____2354 =
                 let uu____2359 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange
                    in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2359  in
               (match uu____2354 with
                | (univs2,t) ->
                    let uu____2362 =
                      let uu____2375 =
                        let uu____2376 = FStar_Syntax_Subst.compress t  in
                        uu____2376.FStar_Syntax_Syntax.n  in
                      match uu____2375 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2417 -> failwith "impossible"  in
                    (match uu____2362 with
                     | (tps1,c1) ->
                         let uu____2448 = sli l  in
                         let uu____2449 = univ_names_to_string univs2  in
                         let uu____2450 = binders_to_string " " tps1  in
                         let uu____2451 = comp_to_string c1  in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2448 uu____2449 uu____2450 uu____2451))
             else
               (let uu____2453 = sli l  in
                let uu____2454 = binders_to_string " " tps  in
                let uu____2455 = comp_to_string c  in
                FStar_Util.format3 "effect %s %s = %s" uu____2453 uu____2454
                  uu____2455)
          in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2456 ->
           let attrs =
             FStar_All.pipe_right x.FStar_Syntax_Syntax.sigattrs
               (FStar_List.map term_to_string)
              in
           let uu____2466 =
             FStar_All.pipe_right attrs (FStar_String.concat " ")  in
           FStar_Util.format2 "[@%s]\n%s" uu____2466 basic)
  
let format_error : FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2475 = FStar_Range.string_of_range r  in
      FStar_Util.format2 "%s: %s\n" uu____2475 msg
  
let rec sigelt_to_string_short : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2479,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2481;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2483;
                       FStar_Syntax_Syntax.lbdef = uu____2484;_}::[]),uu____2485)
        ->
        let uu____2508 = lbname_to_string lb  in
        let uu____2509 = term_to_string t  in
        FStar_Util.format2 "let %s : %s" uu____2508 uu____2509
    | uu____2510 ->
        let uu____2511 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str))
           in
        FStar_All.pipe_right uu____2511 (FStar_String.concat ", ")
  
let rec modul_to_string : FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2525 = sli m.FStar_Syntax_Syntax.name  in
    let uu____2526 =
      let uu____2527 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations
         in
      FStar_All.pipe_right uu____2527 (FStar_String.concat "\n")  in
    FStar_Util.format2 "module %s\n%s" uu____2525 uu____2526
  
let subst_elt_to_string : FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___126_2534  ->
    match uu___126_2534 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2537 = FStar_Util.string_of_int i  in
        let uu____2538 = bv_to_string x  in
        FStar_Util.format2 "DB (%s, %s)" uu____2537 uu____2538
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2541 = bv_to_string x  in
        let uu____2542 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "NM (%s, %s)" uu____2541 uu____2542
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2549 = bv_to_string x  in
        let uu____2550 = term_to_string t  in
        FStar_Util.format2 "DB (%s, %s)" uu____2549 uu____2550
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2553 = FStar_Util.string_of_int i  in
        let uu____2554 = univ_to_string u  in
        FStar_Util.format2 "UN (%s, %s)" uu____2553 uu____2554
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2557 = FStar_Util.string_of_int i  in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2557
  
let subst_to_string : FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2561 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string)  in
    FStar_All.pipe_right uu____2561 (FStar_String.concat "; ")
  
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
           (let uu____2629 = f x  in
            FStar_Util.string_builder_append strb uu____2629);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2636 = f x1  in
                 FStar_Util.string_builder_append strb uu____2636)) xs;
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
           (let uu____2669 = f x  in
            FStar_Util.string_builder_append strb uu____2669);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2676 = f x1  in
                 FStar_Util.string_builder_append strb uu____2676)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)
  