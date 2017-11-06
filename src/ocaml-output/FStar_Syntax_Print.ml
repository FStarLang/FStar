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
    let uu____902 =
      let uu____903 = FStar_Options.ugly () in Prims.op_Negation uu____903 in
    if uu____902
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____907 = FStar_Syntax_Subst.compress_univ u in
       match uu____907 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____919 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____919
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____921 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____921 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____935 = univ_to_string u2 in
                let uu____936 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____935 uu____936)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____940 =
             let uu____941 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____941 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____940
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____953 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____953 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____965 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____965 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___254_974  ->
    match uu___254_974 with
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
        let uu____976 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____976
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____979 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____979 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____990 =
          let uu____991 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____991 in
        let uu____994 =
          let uu____995 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____995 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____990 uu____994
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1014 =
          let uu____1015 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1015 in
        let uu____1018 =
          let uu____1019 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1019 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1014 uu____1018
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1029 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1029
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
    | uu____1038 ->
        let uu____1041 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1041 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1057 ->
        let uu____1060 = quals_to_string quals in Prims.strcat uu____1060 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1116 =
      let uu____1117 = FStar_Options.ugly () in Prims.op_Negation uu____1117 in
    if uu____1116
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1123 = FStar_Options.print_implicits () in
         if uu____1123 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1125 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1150,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1186 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1216 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1234  ->
                                 match uu____1234 with
                                 | (t1,uu____1240) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1216
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1186 (FStar_String.concat "\\/") in
           let uu____1245 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1245
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1257 = tag_of_term t in
           let uu____1258 = sli m in
           let uu____1259 = term_to_string t' in
           let uu____1260 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1257 uu____1258
             uu____1259 uu____1260
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1273 = tag_of_term t in
           let uu____1274 = term_to_string t' in
           let uu____1275 = sli m0 in
           let uu____1276 = sli m1 in
           let uu____1277 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1273
             uu____1274 uu____1275 uu____1276 uu____1277
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1279,s,uu____1281)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1298 = FStar_Range.string_of_range r in
           let uu____1299 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1298
             uu____1299
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1306 = lid_to_string l in
           let uu____1307 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1308 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1306 uu____1307
             uu____1308
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1310) ->
           let uu____1315 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1315
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1317 = db_to_string x3 in
           let uu____1318 =
             let uu____1319 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1319 in
           Prims.strcat uu____1317 uu____1318
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1323) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1350 = FStar_Options.print_universes () in
           if uu____1350
           then
             let uu____1351 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1351
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1371 = binders_to_string " -> " bs in
           let uu____1372 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1371 uu____1372
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1397 = binders_to_string " " bs in
                let uu____1398 = term_to_string t2 in
                let uu____1399 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1403 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1403) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1397 uu____1398
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1399
            | uu____1406 ->
                let uu____1409 = binders_to_string " " bs in
                let uu____1410 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1409 uu____1410)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1417 = bv_to_string xt in
           let uu____1418 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1421 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1417 uu____1418 uu____1421
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1446 = term_to_string t in
           let uu____1447 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1446 uu____1447
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1466 = lbs_to_string [] lbs in
           let uu____1467 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1466 uu____1467
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1528 =
                   let uu____1529 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1529
                     (FStar_Util.dflt "default") in
                 let uu____1534 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1528 uu____1534
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1550 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1550 in
           let uu____1551 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1551 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1590 = term_to_string head1 in
           let uu____1591 =
             let uu____1592 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1628  ->
                       match uu____1628 with
                       | (p,wopt,e) ->
                           let uu____1644 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1645 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1647 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1647 in
                           let uu____1648 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1644
                             uu____1645 uu____1648)) in
             FStar_Util.concat_l "\n\t|" uu____1592 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1590 uu____1591
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1655 = FStar_Options.print_universes () in
           if uu____1655
           then
             let uu____1656 = term_to_string t in
             let uu____1657 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1656 uu____1657
           else term_to_string t
       | uu____1659 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1661 =
      let uu____1662 = FStar_Options.ugly () in Prims.op_Negation uu____1662 in
    if uu____1661
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1684 = fv_to_string l in
           let uu____1685 =
             let uu____1686 =
               FStar_List.map
                 (fun uu____1697  ->
                    match uu____1697 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1686 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1684 uu____1685
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1709) ->
           let uu____1714 = FStar_Options.print_bound_var_types () in
           if uu____1714
           then
             let uu____1715 = bv_to_string x1 in
             let uu____1716 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1715 uu____1716
           else
             (let uu____1718 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1718)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1720 = FStar_Options.print_bound_var_types () in
           if uu____1720
           then
             let uu____1721 = bv_to_string x1 in
             let uu____1722 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1721 uu____1722
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1726 = FStar_Options.print_real_names () in
           if uu____1726
           then
             let uu____1727 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1727
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1746 = FStar_Options.print_universes () in
        if uu____1746
        then
          let uu____1753 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1771 =
                      let uu____1776 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1776 in
                    match uu____1771 with
                    | (us,td) ->
                        let uu____1779 =
                          let uu____1788 =
                            let uu____1789 = FStar_Syntax_Subst.compress td in
                            uu____1789.FStar_Syntax_Syntax.n in
                          match uu____1788 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1800,(t,uu____1802)::(d,uu____1804)::[])
                              -> (t, d)
                          | uu____1847 -> failwith "Impossibe" in
                        (match uu____1779 with
                         | (t,d) ->
                             let uu___261_1866 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___261_1866.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___261_1866.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1753)
        else lbs in
      let uu____1872 = quals_to_string' quals in
      let uu____1873 =
        let uu____1874 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1889 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1890 =
                    let uu____1891 = FStar_Options.print_universes () in
                    if uu____1891
                    then
                      let uu____1892 =
                        let uu____1893 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1893 ">" in
                      Prims.strcat "<" uu____1892
                    else "" in
                  let uu____1895 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1896 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1889 uu____1890
                    uu____1895 uu____1896)) in
        FStar_Util.concat_l "\n and " uu____1874 in
      FStar_Util.format3 "%slet %s %s" uu____1872
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1873
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1903 = FStar_Options.print_effect_args () in
    if uu____1903
    then
      let uu____1904 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1904
    else
      (let uu____1906 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1907 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1906 uu____1907)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___255_1909  ->
      match uu___255_1909 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1912 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1917 =
        let uu____1918 = FStar_Options.ugly () in
        Prims.op_Negation uu____1918 in
      if uu____1917
      then
        let uu____1919 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1919 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1925 = b in
         match uu____1925 with
         | (a,imp) ->
             let uu____1928 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1928
             then
               let uu____1929 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1929
             else
               (let uu____1931 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1933 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1933) in
                if uu____1931
                then
                  let uu____1934 = nm_to_string a in
                  imp_to_string uu____1934 imp
                else
                  (let uu____1936 =
                     let uu____1937 = nm_to_string a in
                     let uu____1938 =
                       let uu____1939 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1939 in
                     Prims.strcat uu____1937 uu____1938 in
                   imp_to_string uu____1936 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1945 = FStar_Options.print_implicits () in
        if uu____1945 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1947 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1947 (FStar_String.concat sep)
      else
        (let uu____1955 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1955 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___256_1962  ->
    match uu___256_1962 with
    | (a,imp) ->
        let uu____1975 = term_to_string a in imp_to_string uu____1975 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1978 = FStar_Options.print_implicits () in
      if uu____1978 then args else filter_imp args in
    let uu____1982 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1982 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1996 =
      let uu____1997 = FStar_Options.ugly () in Prims.op_Negation uu____1997 in
    if uu____1996
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____2011 =
             let uu____2012 = FStar_Syntax_Subst.compress t in
             uu____2012.FStar_Syntax_Syntax.n in
           (match uu____2011 with
            | FStar_Syntax_Syntax.Tm_type uu____2015 when
                let uu____2016 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2016 -> term_to_string t
            | uu____2017 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2019 = univ_to_string u in
                     let uu____2020 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____2019 uu____2020
                 | uu____2021 ->
                     let uu____2024 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____2024))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____2035 =
             let uu____2036 = FStar_Syntax_Subst.compress t in
             uu____2036.FStar_Syntax_Syntax.n in
           (match uu____2035 with
            | FStar_Syntax_Syntax.Tm_type uu____2039 when
                let uu____2040 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____2040 -> term_to_string t
            | uu____2041 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____2043 = univ_to_string u in
                     let uu____2044 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____2043 uu____2044
                 | uu____2045 ->
                     let uu____2048 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____2048))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____2051 = FStar_Options.print_effect_args () in
             if uu____2051
             then
               let uu____2052 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____2053 =
                 let uu____2054 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____2054 (FStar_String.concat ", ") in
               let uu____2061 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____2062 =
                 let uu____2063 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____2063 (FStar_String.concat ", ") in
               let uu____2084 =
                 let uu____2085 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____2085 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____2052
                 uu____2053 uu____2061 uu____2062 uu____2084
             else
               (let uu____2095 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___257_2099  ->
                           match uu___257_2099 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____2100 -> false)))
                    &&
                    (let uu____2102 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____2102) in
                if uu____2095
                then
                  let uu____2103 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____2103
                else
                  (let uu____2105 =
                     ((let uu____2108 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____2108) &&
                        (let uu____2110 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____2110))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____2105
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____2112 =
                        (let uu____2115 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____2115) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___258_2119  ->
                                   match uu___258_2119 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____2120 -> false))) in
                      if uu____2112
                      then
                        let uu____2121 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2121
                      else
                        (let uu____2123 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2124 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2123 uu____2124)))) in
           let dec =
             let uu____2126 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___259_2136  ->
                       match uu___259_2136 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2142 =
                             let uu____2143 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2143 in
                           [uu____2142]
                       | uu____2144 -> [])) in
             FStar_All.pipe_right uu____2126 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2148 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2157 = b in
    match uu____2157 with
    | (a,imp) ->
        let n1 =
          let uu____2161 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2161
          then FStar_Util.JsonNull
          else
            (let uu____2163 =
               let uu____2164 = nm_to_string a in
               imp_to_string uu____2164 imp in
             FStar_Util.JsonStr uu____2163) in
        let t =
          let uu____2166 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2166 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2182 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2182
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2188 = FStar_Options.print_universes () in
    if uu____2188 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2193 =
      let uu____2194 = FStar_Options.ugly () in Prims.op_Negation uu____2194 in
    if uu____2193
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2198 = s in
       match uu____2198 with
       | (us,t) ->
           let uu____2205 =
             let uu____2206 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2206 in
           let uu____2207 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2205 uu____2207)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2211 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2212 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2213 =
      let uu____2214 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2214 in
    let uu____2215 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2216 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2211 uu____2212 uu____2213
      uu____2215 uu____2216
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
          let uu____2233 =
            let uu____2234 = FStar_Options.ugly () in
            Prims.op_Negation uu____2234 in
          if uu____2233
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2246 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2246 (FStar_String.concat ",\n\t") in
             let uu____2255 =
               let uu____2258 =
                 let uu____2261 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2262 =
                   let uu____2265 =
                     let uu____2266 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2266 in
                   let uu____2267 =
                     let uu____2270 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2271 =
                       let uu____2274 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2275 =
                         let uu____2278 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2279 =
                           let uu____2282 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2283 =
                             let uu____2286 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2287 =
                               let uu____2290 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2291 =
                                 let uu____2294 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2295 =
                                   let uu____2298 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2299 =
                                     let uu____2302 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2303 =
                                       let uu____2306 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2307 =
                                         let uu____2310 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2311 =
                                           let uu____2314 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2315 =
                                             let uu____2318 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2319 =
                                               let uu____2322 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2323 =
                                                 let uu____2326 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2327 =
                                                   let uu____2330 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2330] in
                                                 uu____2326 :: uu____2327 in
                                               uu____2322 :: uu____2323 in
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
                   uu____2265 :: uu____2267 in
                 uu____2261 :: uu____2262 in
               (if for_free then "_for_free " else "") :: uu____2258 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2255)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2341 =
      let uu____2342 = FStar_Options.ugly () in Prims.op_Negation uu____2342 in
    if uu____2341
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2348 -> ""
    else
      (match x.FStar_Syntax_Syntax.sigel with
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
           (lid,univs1,tps,k,uu____2358,uu____2359) ->
           let uu____2368 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2369 = binders_to_string " " tps in
           let uu____2370 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2368
             lid.FStar_Ident.str uu____2369 uu____2370
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2374,uu____2375,uu____2376) ->
           let uu____2381 = FStar_Options.print_universes () in
           if uu____2381
           then
             let uu____2382 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2382 with
              | (univs2,t1) ->
                  let uu____2389 = univ_names_to_string univs2 in
                  let uu____2390 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2389
                    lid.FStar_Ident.str uu____2390)
           else
             (let uu____2392 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2392)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2396 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2396 with
            | (univs2,t1) ->
                let uu____2403 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2404 =
                  let uu____2405 = FStar_Options.print_universes () in
                  if uu____2405
                  then
                    let uu____2406 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2406
                  else "" in
                let uu____2408 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2403
                  lid.FStar_Ident.str uu____2404 uu____2408)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2410,f) ->
           let uu____2412 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2412
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2414) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2420 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2420
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2422) ->
           let uu____2431 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2431 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None )
                 -> failwith "impossible"
             | (FStar_Pervasives_Native.Some lift_wp,uu____2449) -> lift_wp
             | (uu____2456,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2464 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2464 with
            | (us,t) ->
                let uu____2475 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2476 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2477 = univ_names_to_string us in
                let uu____2478 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2475
                  uu____2476 uu____2477 uu____2478)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2488 = FStar_Options.print_universes () in
           if uu____2488
           then
             let uu____2489 =
               let uu____2494 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2494 in
             (match uu____2489 with
              | (univs2,t) ->
                  let uu____2497 =
                    let uu____2510 =
                      let uu____2511 = FStar_Syntax_Subst.compress t in
                      uu____2511.FStar_Syntax_Syntax.n in
                    match uu____2510 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2552 -> failwith "impossible" in
                  (match uu____2497 with
                   | (tps1,c1) ->
                       let uu____2583 = sli l in
                       let uu____2584 = univ_names_to_string univs2 in
                       let uu____2585 = binders_to_string " " tps1 in
                       let uu____2586 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2583
                         uu____2584 uu____2585 uu____2586))
           else
             (let uu____2588 = sli l in
              let uu____2589 = binders_to_string " " tps in
              let uu____2590 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2588 uu____2589
                uu____2590))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2597 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2597 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2601,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2603;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2605;
                       FStar_Syntax_Syntax.lbdef = uu____2606;_}::[]),uu____2607)
        ->
        let uu____2630 = lbname_to_string lb in
        let uu____2631 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2630 uu____2631
    | uu____2632 ->
        let uu____2633 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2633 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2647 = sli m.FStar_Syntax_Syntax.name in
    let uu____2648 =
      let uu____2649 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2649 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2647 uu____2648
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___260_2656  ->
    match uu___260_2656 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2659 = FStar_Util.string_of_int i in
        let uu____2660 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2659 uu____2660
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2663 = bv_to_string x in
        let uu____2664 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2663 uu____2664
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2671 = bv_to_string x in
        let uu____2672 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2671 uu____2672
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2675 = FStar_Util.string_of_int i in
        let uu____2676 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2675 uu____2676
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2679 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2679
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2683 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2683 (FStar_String.concat "; ")
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
           (let uu____2751 = f x in
            FStar_Util.string_builder_append strb uu____2751);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2758 = f x1 in
                 FStar_Util.string_builder_append strb uu____2758)) xs;
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
           (let uu____2791 = f x in
            FStar_Util.string_builder_append strb uu____2791);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2798 = f x1 in
                 FStar_Util.string_builder_append strb uu____2798)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)