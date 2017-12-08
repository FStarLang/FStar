open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___250_3  ->
    match uu___250_3 with
    | FStar_Syntax_Syntax.Delta_constant  -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____5 = FStar_Util.string_of_int i in
        Prims.strcat "Delta_defined_at_level " uu____5
    | FStar_Syntax_Syntax.Delta_equational  -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____7 =
          let uu____8 = delta_depth_to_string d in Prims.strcat uu____8 ")" in
        Prims.strcat "Delta_abstract (" uu____7
let sli: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____12 = FStar_Options.print_real_names () in
    if uu____12
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let lid_to_string: FStar_Ident.lid -> Prims.string = fun l  -> sli l
let fv_to_string: FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let bv_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____23 =
      let uu____24 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____24 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____23
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____28 = FStar_Options.print_real_names () in
    if uu____28
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____33 =
      let uu____34 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____34 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____33
let infix_prim_ops:
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
let unary_prim_ops:
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  [(FStar_Parser_Const.op_Negation, "not");
  (FStar_Parser_Const.op_Minus, "-");
  (FStar_Parser_Const.not_lid, "~")]
let is_prim_op:
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
let get_lid:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident
  =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____177 -> failwith "get_lid"
let is_infix_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split infix_prim_ops)) e
let is_unary_prim_op: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    is_prim_op
      (FStar_Pervasives_Native.fst (FStar_List.split unary_prim_ops)) e
let quants:
  (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list
  =
  [(FStar_Parser_Const.forall_lid, "forall");
  (FStar_Parser_Const.exists_lid, "exists")]
type exp = FStar_Syntax_Syntax.term[@@deriving show]
let is_b2t: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Parser_Const.b2t_lid] t
let is_quant: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    is_prim_op (FStar_Pervasives_Native.fst (FStar_List.split quants)) t
let is_ite: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  -> is_prim_op [FStar_Parser_Const.ite_lid] t
let is_lex_cons: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Parser_Const.lexcons_lid] f
let is_lex_top: exp -> Prims.bool =
  fun f  -> is_prim_op [FStar_Parser_Const.lextop_lid] f
let is_inr:
  'Auu____232 'Auu____233 .
    ('Auu____233,'Auu____232) FStar_Util.either -> Prims.bool
  =
  fun uu___251_241  ->
    match uu___251_241 with
    | FStar_Util.Inl uu____246 -> false
    | FStar_Util.Inr uu____247 -> true
let filter_imp:
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
         (fun uu___252_304  ->
            match uu___252_304 with
            | (uu____311,FStar_Pervasives_Native.Some
               (FStar_Syntax_Syntax.Implicit uu____312)) -> false
            | uu____315 -> true))
let rec reconstruct_lex:
  exp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
      FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____331 =
      let uu____332 = FStar_Syntax_Subst.compress e in
      uu____332.FStar_Syntax_Syntax.n in
    match uu____331 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____395 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____395
        then
          let uu____404 =
            let uu____411 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____411 in
          (match uu____404 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____429 =
                 let uu____434 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____434 :: xs in
               FStar_Pervasives_Native.Some uu____429
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____458 ->
        let uu____459 = is_lex_top e in
        if uu____459
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find: 'a . ('a -> Prims.bool) -> 'a Prims.list -> 'a =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "blah"
      | hd1::tl1 ->
          let uu____502 = f hd1 in if uu____502 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____522 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____522
let infix_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____544 = get_lid e in find_lid uu____544 infix_prim_ops
let unary_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____552 = get_lid e in find_lid uu____552 unary_prim_ops
let quant_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun t  -> let uu____560 = get_lid t in find_lid uu____560 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  -> FStar_Parser_Const.const_to_string x
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___253_566  ->
    match uu___253_566 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____573 = db_to_string x in Prims.strcat "Tm_bvar: " uu____573
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____575 = nm_to_string x in Prims.strcat "Tm_name: " uu____575
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____577 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____577
    | FStar_Syntax_Syntax.Tm_uinst uu____578 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____585 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____586 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____587 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____604 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____617 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____624 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____639 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____662 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____689 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____702 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____719,m) ->
        let uu____761 = FStar_ST.op_Bang m in
        (match uu____761 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____836 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____841 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____851 = FStar_Options.hide_uvar_nums () in
    if uu____851
    then "?"
    else
      (let uu____853 =
         let uu____854 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____854 FStar_Util.string_of_int in
       Prims.strcat "?" uu____853)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____858 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____859 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____858 uu____859
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____863 = FStar_Options.hide_uvar_nums () in
    if uu____863
    then "?"
    else
      (let uu____865 =
         let uu____866 =
           let uu____867 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____867 FStar_Util.string_of_int in
         let uu____868 =
           let uu____869 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____869 in
         Prims.strcat uu____866 uu____868 in
       Prims.strcat "?" uu____865)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____886 = FStar_Syntax_Subst.compress_univ u in
      match uu____886 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____896 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____902 = FStar_Syntax_Subst.compress_univ u in
    match uu____902 with
    | FStar_Syntax_Syntax.U_unif u1 ->
        let uu____912 = univ_uvar_to_string u1 in
        Prims.strcat "U_unif " uu____912
    | FStar_Syntax_Syntax.U_name x ->
        Prims.strcat "U_name " x.FStar_Ident.idText
    | FStar_Syntax_Syntax.U_bvar x ->
        let uu____915 = FStar_Util.string_of_int x in
        Prims.strcat "@" uu____915
    | FStar_Syntax_Syntax.U_zero  -> "0"
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____917 = int_of_univ (Prims.parse_int "1") u1 in
        (match uu____917 with
         | (n1,FStar_Pervasives_Native.None ) -> FStar_Util.string_of_int n1
         | (n1,FStar_Pervasives_Native.Some u2) ->
             let uu____931 = univ_to_string u2 in
             let uu____932 = FStar_Util.string_of_int n1 in
             FStar_Util.format2 "(%s + %s)" uu____931 uu____932)
    | FStar_Syntax_Syntax.U_max us ->
        let uu____936 =
          let uu____937 = FStar_List.map univ_to_string us in
          FStar_All.pipe_right uu____937 (FStar_String.concat ", ") in
        FStar_Util.format1 "(max %s)" uu____936
    | FStar_Syntax_Syntax.U_unknown  -> "unknown"
let univs_to_string: FStar_Syntax_Syntax.universes -> Prims.string =
  fun us  ->
    let uu____945 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____945 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____957 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____957 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___254_966  ->
    match uu___254_966 with
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
        let uu____968 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____968
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____971 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____971 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____982 =
          let uu____983 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____983 in
        let uu____986 =
          let uu____987 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____987 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____982 uu____986
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1006 =
          let uu____1007 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1007 in
        let uu____1010 =
          let uu____1011 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1011 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1006 uu____1010
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1021 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1021
    | FStar_Syntax_Syntax.ExceptionConstructor  -> "ExceptionConstructor"
    | FStar_Syntax_Syntax.HasMaskedEffect  -> "HasMaskedEffect"
    | FStar_Syntax_Syntax.Effect  -> "Effect"
    | FStar_Syntax_Syntax.Reifiable  -> "reify"
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Util.format1 "(reflect %s)" l.FStar_Ident.str
    | FStar_Syntax_Syntax.OnlyName  -> "OnlyName"
let quals_to_string: FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string
  =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1030 ->
        let uu____1033 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1033 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1049 ->
        let uu____1052 = quals_to_string quals in Prims.strcat uu____1052 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1108 =
      let uu____1109 = FStar_Options.ugly () in Prims.op_Negation uu____1109 in
    if uu____1108
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1115 = FStar_Options.print_implicits () in
         if uu____1115 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1117 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1142,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1178 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1208 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1226  ->
                                 match uu____1226 with
                                 | (t1,uu____1232) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1208
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1178 (FStar_String.concat "\\/") in
           let uu____1237 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1237
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1249 = tag_of_term t in
           let uu____1250 = sli m in
           let uu____1251 = term_to_string t' in
           let uu____1252 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1249 uu____1250
             uu____1251 uu____1252
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1265 = tag_of_term t in
           let uu____1266 = term_to_string t' in
           let uu____1267 = sli m0 in
           let uu____1268 = sli m1 in
           let uu____1269 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1265
             uu____1266 uu____1267 uu____1268 uu____1269
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1271,s,uu____1273)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1290 = FStar_Range.string_of_range r in
           let uu____1291 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1290
             uu____1291
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1298 = lid_to_string l in
           let uu____1299 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1300 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1298 uu____1299
             uu____1300
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1302) ->
           let uu____1307 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1307
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1309 = db_to_string x3 in
           let uu____1310 =
             let uu____1311 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1311 in
           Prims.strcat uu____1309 uu____1310
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1315) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1342 = FStar_Options.print_universes () in
           if uu____1342
           then
             let uu____1343 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1343
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1363 = binders_to_string " -> " bs in
           let uu____1364 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1363 uu____1364
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1389 = binders_to_string " " bs in
                let uu____1390 = term_to_string t2 in
                let uu____1391 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1395 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1395) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1389 uu____1390
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1391
            | uu____1398 ->
                let uu____1401 = binders_to_string " " bs in
                let uu____1402 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1401 uu____1402)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1409 = bv_to_string xt in
           let uu____1410 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1413 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1409 uu____1410 uu____1413
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1438 = term_to_string t in
           let uu____1439 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1438 uu____1439
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1458 = lbs_to_string [] lbs in
           let uu____1459 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1458 uu____1459
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1520 =
                   let uu____1521 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1521
                     (FStar_Util.dflt "default") in
                 let uu____1526 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1520 uu____1526
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1542 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1542 in
           let uu____1543 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1543 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1582 = term_to_string head1 in
           let uu____1583 =
             let uu____1584 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1620  ->
                       match uu____1620 with
                       | (p,wopt,e) ->
                           let uu____1636 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1637 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1639 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1639 in
                           let uu____1640 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1636
                             uu____1637 uu____1640)) in
             FStar_Util.concat_l "\n\t|" uu____1584 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1582 uu____1583
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1647 = FStar_Options.print_universes () in
           if uu____1647
           then
             let uu____1648 = term_to_string t in
             let uu____1649 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1648 uu____1649
           else term_to_string t
       | uu____1651 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1653 =
      let uu____1654 = FStar_Options.ugly () in Prims.op_Negation uu____1654 in
    if uu____1653
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1676 = fv_to_string l in
           let uu____1677 =
             let uu____1678 =
               FStar_List.map
                 (fun uu____1689  ->
                    match uu____1689 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1678 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1676 uu____1677
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1701) ->
           let uu____1706 = FStar_Options.print_bound_var_types () in
           if uu____1706
           then
             let uu____1707 = bv_to_string x1 in
             let uu____1708 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1707 uu____1708
           else
             (let uu____1710 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1710)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1712 = FStar_Options.print_bound_var_types () in
           if uu____1712
           then
             let uu____1713 = bv_to_string x1 in
             let uu____1714 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1713 uu____1714
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1718 = FStar_Options.print_real_names () in
           if uu____1718
           then
             let uu____1719 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1719
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1738 = FStar_Options.print_universes () in
        if uu____1738
        then
          let uu____1745 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1763 =
                      let uu____1768 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1768 in
                    match uu____1763 with
                    | (us,td) ->
                        let uu____1771 =
                          let uu____1780 =
                            let uu____1781 = FStar_Syntax_Subst.compress td in
                            uu____1781.FStar_Syntax_Syntax.n in
                          match uu____1780 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1792,(t,uu____1794)::(d,uu____1796)::[])
                              -> (t, d)
                          | uu____1839 -> failwith "Impossibe" in
                        (match uu____1771 with
                         | (t,d) ->
                             let uu___261_1858 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___261_1858.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___261_1858.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1745)
        else lbs in
      let uu____1864 = quals_to_string' quals in
      let uu____1865 =
        let uu____1866 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1881 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1882 =
                    let uu____1883 = FStar_Options.print_universes () in
                    if uu____1883
                    then
                      let uu____1884 =
                        let uu____1885 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1885 ">" in
                      Prims.strcat "<" uu____1884
                    else "" in
                  let uu____1887 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1888 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1881 uu____1882
                    uu____1887 uu____1888)) in
        FStar_Util.concat_l "\n and " uu____1866 in
      FStar_Util.format3 "%slet %s %s" uu____1864
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1865
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1895 = FStar_Options.print_effect_args () in
    if uu____1895
    then
      let uu____1896 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1896
    else
      (let uu____1898 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1899 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1898 uu____1899)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___255_1901  ->
      match uu___255_1901 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1904 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1909 =
        let uu____1910 = FStar_Options.ugly () in
        Prims.op_Negation uu____1910 in
      if uu____1909
      then
        let uu____1911 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1911 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1917 = b in
         match uu____1917 with
         | (a,imp) ->
             let uu____1920 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1920
             then
               let uu____1921 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1921
             else
               (let uu____1923 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1925 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1925) in
                if uu____1923
                then
                  let uu____1926 = nm_to_string a in
                  imp_to_string uu____1926 imp
                else
                  (let uu____1928 =
                     let uu____1929 = nm_to_string a in
                     let uu____1930 =
                       let uu____1931 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1931 in
                     Prims.strcat uu____1929 uu____1930 in
                   imp_to_string uu____1928 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1937 = FStar_Options.print_implicits () in
        if uu____1937 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1939 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1939 (FStar_String.concat sep)
      else
        (let uu____1947 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1947 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___256_1954  ->
    match uu___256_1954 with
    | (a,imp) ->
        let uu____1967 = term_to_string a in imp_to_string uu____1967 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1970 = FStar_Options.print_implicits () in
      if uu____1970 then args else filter_imp args in
    let uu____1974 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1974 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1988 =
      let uu____1989 = FStar_Options.ugly () in Prims.op_Negation uu____1989 in
    if uu____1988
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2003 =
             let uu____2004 = FStar_Syntax_Subst.compress t in
             uu____2004.FStar_Syntax_Syntax.n in
           (match uu____2003 with
            | FStar_Syntax_Syntax.Tm_type uu____2007 when
                let uu____2008 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2008 -> term_to_string t
            | uu____2009 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2011 = univ_to_string u in
                     let uu____2012 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2011 uu____2012
                 | uu____2013 ->
                     let uu____2016 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2016))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2027 =
             let uu____2028 = FStar_Syntax_Subst.compress t in
             uu____2028.FStar_Syntax_Syntax.n in
           (match uu____2027 with
            | FStar_Syntax_Syntax.Tm_type uu____2031 when
                let uu____2032 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2032 -> term_to_string t
            | uu____2033 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2035 = univ_to_string u in
                     let uu____2036 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2035 uu____2036
                 | uu____2037 ->
                     let uu____2040 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2040))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2043 = FStar_Options.print_effect_args () in
             if uu____2043
             then
               let uu____2044 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2045 =
                 let uu____2046 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2046 (FStar_String.concat ", ") in
               let uu____2053 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2054 =
                 let uu____2055 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2055 (FStar_String.concat ", ") in
               let uu____2076 =
                 let uu____2077 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2077 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2044
                 uu____2045 uu____2053 uu____2054 uu____2076
             else
               (let uu____2087 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___257_2091  ->
                           match uu___257_2091 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2092 -> false)))
                    &&
                    (let uu____2094 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2094) in
                if uu____2087
                then
                  let uu____2095 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2095
                else
                  (let uu____2097 =
                     ((let uu____2100 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2100) &&
                        (let uu____2102 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2102))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2097
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2104 =
                        (let uu____2107 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2107) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___258_2111  ->
                                   match uu___258_2111 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2112 -> false))) in
                      if uu____2104
                      then
                        let uu____2113 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2113
                      else
                        (let uu____2115 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2116 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2115 uu____2116)))) in
           let dec =
             let uu____2118 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___259_2128  ->
                       match uu___259_2128 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2134 =
                             let uu____2135 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2135 in
                           [uu____2134]
                       | uu____2136 -> [])) in
             FStar_All.pipe_right uu____2118 (FStar_String.concat " ") in
           FStar_Util.format2 "%s%s" basic dec)
and cflags_to_string: FStar_Syntax_Syntax.cflags -> Prims.string =
  fun c  ->
    match c with
    | FStar_Syntax_Syntax.TOTAL  -> "total"
    | FStar_Syntax_Syntax.MLEFFECT  -> "ml"
    | FStar_Syntax_Syntax.RETURN  -> "return"
    | FStar_Syntax_Syntax.PARTIAL_RETURN  -> "partial_return"
    | FStar_Syntax_Syntax.SOMETRIVIAL  -> "sometrivial"
    | FStar_Syntax_Syntax.LEMMA  -> "lemma"
    | FStar_Syntax_Syntax.CPS  -> "cps"
    | FStar_Syntax_Syntax.DECREASES uu____2140 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2149 = b in
    match uu____2149 with
    | (a,imp) ->
        let n1 =
          let uu____2153 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2153
          then FStar_Util.JsonNull
          else
            (let uu____2155 =
               let uu____2156 = nm_to_string a in
               imp_to_string uu____2156 imp in
             FStar_Util.JsonStr uu____2155) in
        let t =
          let uu____2158 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2158 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2174 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2174
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2180 = FStar_Options.print_universes () in
    if uu____2180 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2185 =
      let uu____2186 = FStar_Options.ugly () in Prims.op_Negation uu____2186 in
    if uu____2185
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2190 = s in
       match uu____2190 with
       | (us,t) ->
           let uu____2197 =
             let uu____2198 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2198 in
           let uu____2199 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2197 uu____2199)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2203 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2204 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2205 =
      let uu____2206 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2206 in
    let uu____2207 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2208 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2203 uu____2204 uu____2205
      uu____2207 uu____2208
let eff_decl_to_string':
  Prims.bool ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl -> Prims.string
  =
  fun for_free  ->
    fun r  ->
      fun q  ->
        fun ed  ->
          let uu____2225 =
            let uu____2226 = FStar_Options.ugly () in
            Prims.op_Negation uu____2226 in
          if uu____2225
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2238 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2238 (FStar_String.concat ",\n\t") in
             let uu____2247 =
               let uu____2250 =
                 let uu____2253 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2254 =
                   let uu____2257 =
                     let uu____2258 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2258 in
                   let uu____2259 =
                     let uu____2262 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2263 =
                       let uu____2266 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2267 =
                         let uu____2270 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2271 =
                           let uu____2274 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2275 =
                             let uu____2278 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2279 =
                               let uu____2282 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2283 =
                                 let uu____2286 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2287 =
                                   let uu____2290 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2291 =
                                     let uu____2294 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2295 =
                                       let uu____2298 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2299 =
                                         let uu____2302 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2303 =
                                           let uu____2306 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2307 =
                                             let uu____2310 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2311 =
                                               let uu____2314 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2315 =
                                                 let uu____2318 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2319 =
                                                   let uu____2322 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2322] in
                                                 uu____2318 :: uu____2319 in
                                               uu____2314 :: uu____2315 in
                                             uu____2310 :: uu____2311 in
                                           uu____2306 :: uu____2307 in
                                         uu____2302 :: uu____2303 in
                                       uu____2298 :: uu____2299 in
                                     uu____2294 :: uu____2295 in
                                   uu____2290 :: uu____2291 in
                                 uu____2286 :: uu____2287 in
                               uu____2282 :: uu____2283 in
                             uu____2278 :: uu____2279 in
                           uu____2274 :: uu____2275 in
                         uu____2270 :: uu____2271 in
                       uu____2266 :: uu____2267 in
                     uu____2262 :: uu____2263 in
                   uu____2257 :: uu____2259 in
                 uu____2253 :: uu____2254 in
               (if for_free then "_for_free " else "") :: uu____2250 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2247)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.LightOff ) ->
        "#light \"off\""
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
        (FStar_Pervasives_Native.None )) -> "#reset-options"
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.ResetOptions
        (FStar_Pervasives_Native.Some s)) ->
        FStar_Util.format1 "#reset-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_pragma (FStar_Syntax_Syntax.SetOptions s) ->
        FStar_Util.format1 "#set-options \"%s\"" s
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,univs1,tps,k,uu____2339,uu____2340) ->
        let uu____2349 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
        let uu____2350 = binders_to_string " " tps in
        let uu____2351 = term_to_string k in
        FStar_Util.format4 "%stype %s %s : %s" uu____2349 lid.FStar_Ident.str
          uu____2350 uu____2351
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,univs1,t,uu____2355,uu____2356,uu____2357) ->
        let uu____2362 = FStar_Options.print_universes () in
        if uu____2362
        then
          let uu____2363 = FStar_Syntax_Subst.open_univ_vars univs1 t in
          (match uu____2363 with
           | (univs2,t1) ->
               let uu____2370 = univ_names_to_string univs2 in
               let uu____2371 = term_to_string t1 in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2370
                 lid.FStar_Ident.str uu____2371)
        else
          (let uu____2373 = term_to_string t in
           FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
             uu____2373)
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
        let uu____2377 = FStar_Syntax_Subst.open_univ_vars univs1 t in
        (match uu____2377 with
         | (univs2,t1) ->
             let uu____2384 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let uu____2385 =
               let uu____2386 = FStar_Options.print_universes () in
               if uu____2386
               then
                 let uu____2387 = univ_names_to_string univs2 in
                 FStar_Util.format1 "<%s>" uu____2387
               else "" in
             let uu____2389 = term_to_string t1 in
             FStar_Util.format4 "%sval %s %s : %s" uu____2384
               lid.FStar_Ident.str uu____2385 uu____2389)
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2391,f) ->
        let uu____2393 = term_to_string f in
        FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2393
    | FStar_Syntax_Syntax.Sig_let (lbs,uu____2395) ->
        lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
    | FStar_Syntax_Syntax.Sig_main e ->
        let uu____2401 = term_to_string e in
        FStar_Util.format1 "let _ = %s" uu____2401
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2403) ->
        let uu____2412 = FStar_List.map sigelt_to_string ses in
        FStar_All.pipe_right uu____2412 (FStar_String.concat "\n")
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
          | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
              failwith "impossible"
          | (FStar_Pervasives_Native.Some lift_wp,uu____2430) -> lift_wp
          | (uu____2437,FStar_Pervasives_Native.Some lift) -> lift in
        let uu____2445 =
          FStar_Syntax_Subst.open_univ_vars
            (FStar_Pervasives_Native.fst lift_wp)
            (FStar_Pervasives_Native.snd lift_wp) in
        (match uu____2445 with
         | (us,t) ->
             let uu____2456 = lid_to_string se.FStar_Syntax_Syntax.source in
             let uu____2457 = lid_to_string se.FStar_Syntax_Syntax.target in
             let uu____2458 = univ_names_to_string us in
             let uu____2459 = term_to_string t in
             FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2456
               uu____2457 uu____2458 uu____2459)
    | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
        let uu____2469 = FStar_Options.print_universes () in
        if uu____2469
        then
          let uu____2470 =
            let uu____2475 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                FStar_Pervasives_Native.None FStar_Range.dummyRange in
            FStar_Syntax_Subst.open_univ_vars univs1 uu____2475 in
          (match uu____2470 with
           | (univs2,t) ->
               let uu____2478 =
                 let uu____2491 =
                   let uu____2492 = FStar_Syntax_Subst.compress t in
                   uu____2492.FStar_Syntax_Syntax.n in
                 match uu____2491 with
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                 | uu____2533 -> failwith "impossible" in
               (match uu____2478 with
                | (tps1,c1) ->
                    let uu____2564 = sli l in
                    let uu____2565 = univ_names_to_string univs2 in
                    let uu____2566 = binders_to_string " " tps1 in
                    let uu____2567 = comp_to_string c1 in
                    FStar_Util.format4 "effect %s<%s> %s = %s" uu____2564
                      uu____2565 uu____2566 uu____2567))
        else
          (let uu____2569 = sli l in
           let uu____2570 = binders_to_string " " tps in
           let uu____2571 = comp_to_string c in
           FStar_Util.format3 "effect %s %s = %s" uu____2569 uu____2570
             uu____2571)
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2578 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2578 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2582,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2584;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2586;
                       FStar_Syntax_Syntax.lbdef = uu____2587;_}::[]),uu____2588)
        ->
        let uu____2611 = lbname_to_string lb in
        let uu____2612 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2611 uu____2612
    | uu____2613 ->
        let uu____2614 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2614 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2628 = sli m.FStar_Syntax_Syntax.name in
    let uu____2629 =
      let uu____2630 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2630 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2628 uu____2629
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___260_2637  ->
    match uu___260_2637 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2640 = FStar_Util.string_of_int i in
        let uu____2641 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2640 uu____2641
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2644 = bv_to_string x in
        let uu____2645 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2644 uu____2645
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2652 = bv_to_string x in
        let uu____2653 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2652 uu____2653
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2656 = FStar_Util.string_of_int i in
        let uu____2657 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2656 uu____2657
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2660 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2660
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2664 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2664 (FStar_String.concat "; ")
let abs_ascription_to_string:
  (FStar_Syntax_Syntax.lcomp,FStar_Ident.lident) FStar_Util.either
    FStar_Pervasives_Native.option -> Prims.string
  =
  fun ascription  ->
    let strb = FStar_Util.new_string_builder () in
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
let list_to_string:
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun elts  ->
      match elts with
      | [] -> "[]"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "[";
           (let uu____2732 = f x in
            FStar_Util.string_builder_append strb uu____2732);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2739 = f x1 in
                 FStar_Util.string_builder_append strb uu____2739)) xs;
           FStar_Util.string_builder_append strb "]";
           FStar_Util.string_of_string_builder strb)
let set_to_string:
  'a . ('a -> Prims.string) -> 'a FStar_Util.set -> Prims.string =
  fun f  ->
    fun s  ->
      let elts = FStar_Util.set_elements s in
      match elts with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Util.new_string_builder () in
          (FStar_Util.string_builder_append strb "{";
           (let uu____2772 = f x in
            FStar_Util.string_builder_append strb uu____2772);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2779 = f x1 in
                 FStar_Util.string_builder_append strb uu____2779)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)