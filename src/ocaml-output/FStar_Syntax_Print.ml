
open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___111_3  ->
    match uu___111_3 with
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
  fun uu___112_241  ->
    match uu___112_241 with
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
         (fun uu___113_304  ->
            match uu___113_304 with
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
          let uu____503 = f hd1 in if uu____503 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____523 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____523
let infix_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____545 = get_lid e in find_lid uu____545 infix_prim_ops
let unary_prim_op_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun e  -> let uu____553 = get_lid e in find_lid uu____553 unary_prim_ops
let quant_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun t  -> let uu____561 = get_lid t in find_lid uu____561 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  -> FStar_Parser_Const.const_to_string x
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___114_567  ->
    match uu___114_567 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____574 = db_to_string x in Prims.strcat "Tm_bvar: " uu____574
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____576 = nm_to_string x in Prims.strcat "Tm_name: " uu____576
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____578 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
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
        let uu____762 = FStar_ST.op_Bang m in
        (match uu____762 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____837 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____842 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____852 = FStar_Options.hide_uvar_nums () in
    if uu____852
    then "?"
    else
      (let uu____854 =
         let uu____855 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____855 FStar_Util.string_of_int in
       Prims.strcat "?" uu____854)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____859 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____860 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____859 uu____860
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____864 = FStar_Options.hide_uvar_nums () in
    if uu____864
    then "?"
    else
      (let uu____866 =
         let uu____867 =
           let uu____868 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____868 FStar_Util.string_of_int in
         let uu____869 =
           let uu____870 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____870 in
         Prims.strcat uu____867 uu____869 in
       Prims.strcat "?" uu____866)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____887 = FStar_Syntax_Subst.compress_univ u in
      match uu____887 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____897 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____903 =
      let uu____904 = FStar_Options.ugly () in Prims.op_Negation uu____904 in
    if uu____903
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____908 = FStar_Syntax_Subst.compress_univ u in
       match uu____908 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____920 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____920
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____922 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____922 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____936 = univ_to_string u2 in
                let uu____937 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____936 uu____937)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____941 =
             let uu____942 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____942 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____941
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____954 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____954 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____966 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____966 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___115_975  ->
    match uu___115_975 with
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
        let uu____977 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____977
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____980 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____980 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____991 =
          let uu____992 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____992 in
        let uu____995 =
          let uu____996 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____996 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____991 uu____995
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1015 =
          let uu____1016 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1016 in
        let uu____1019 =
          let uu____1020 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1020 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1015 uu____1019
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1030 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1030
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
    | uu____1039 ->
        let uu____1042 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1042 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1058 ->
        let uu____1061 = quals_to_string quals in Prims.strcat uu____1061 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1117 =
      let uu____1118 = FStar_Options.ugly () in Prims.op_Negation uu____1118 in
    if uu____1117
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1124 = FStar_Options.print_implicits () in
         if uu____1124 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1126 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1151,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1187 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1217 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1235  ->
                                 match uu____1235 with
                                 | (t1,uu____1241) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1217
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1187 (FStar_String.concat "\\/") in
           let uu____1246 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1246
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1258 = tag_of_term t in
           let uu____1259 = sli m in
           let uu____1260 = term_to_string t' in
           let uu____1261 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1258 uu____1259
             uu____1260 uu____1261
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1274 = tag_of_term t in
           let uu____1275 = term_to_string t' in
           let uu____1276 = sli m0 in
           let uu____1277 = sli m1 in
           let uu____1278 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1274
             uu____1275 uu____1276 uu____1277 uu____1278
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1280,s,uu____1282)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1299 = FStar_Range.string_of_range r in
           let uu____1300 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1299
             uu____1300
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1307 = lid_to_string l in
           let uu____1308 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1309 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1307 uu____1308
             uu____1309
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1311) ->
           let uu____1316 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1316
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1318 = db_to_string x3 in
           let uu____1319 =
             let uu____1320 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1320 in
           Prims.strcat uu____1318 uu____1319
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1324) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1351 = FStar_Options.print_universes () in
           if uu____1351
           then
             let uu____1352 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1352
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1372 = binders_to_string " -> " bs in
           let uu____1373 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1372 uu____1373
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1398 = binders_to_string " " bs in
                let uu____1399 = term_to_string t2 in
                let uu____1400 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1404 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1404) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1398 uu____1399
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1400
            | uu____1407 ->
                let uu____1410 = binders_to_string " " bs in
                let uu____1411 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1410 uu____1411)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1418 = bv_to_string xt in
           let uu____1419 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1422 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1418 uu____1419 uu____1422
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1447 = term_to_string t in
           let uu____1448 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1447 uu____1448
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1467 = lbs_to_string [] lbs in
           let uu____1468 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1467 uu____1468
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1529 =
                   let uu____1530 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1530
                     (FStar_Util.dflt "default") in
                 let uu____1535 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1529 uu____1535
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1551 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1551 in
           let uu____1552 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1552 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1591 = term_to_string head1 in
           let uu____1592 =
             let uu____1593 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1629  ->
                       match uu____1629 with
                       | (p,wopt,e) ->
                           let uu____1645 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1646 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1648 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1648 in
                           let uu____1649 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1645
                             uu____1646 uu____1649)) in
             FStar_Util.concat_l "\n\t|" uu____1593 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1591 uu____1592
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1656 = FStar_Options.print_universes () in
           if uu____1656
           then
             let uu____1657 = term_to_string t in
             let uu____1658 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1657 uu____1658
           else term_to_string t
       | uu____1660 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1662 =
      let uu____1663 = FStar_Options.ugly () in Prims.op_Negation uu____1663 in
    if uu____1662
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1685 = fv_to_string l in
           let uu____1686 =
             let uu____1687 =
               FStar_List.map
                 (fun uu____1698  ->
                    match uu____1698 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1687 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1685 uu____1686
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1710) ->
           let uu____1715 = FStar_Options.print_bound_var_types () in
           if uu____1715
           then
             let uu____1716 = bv_to_string x1 in
             let uu____1717 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1716 uu____1717
           else
             (let uu____1719 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1719)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1721 = FStar_Options.print_bound_var_types () in
           if uu____1721
           then
             let uu____1722 = bv_to_string x1 in
             let uu____1723 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1722 uu____1723
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1727 = FStar_Options.print_real_names () in
           if uu____1727
           then
             let uu____1728 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1728
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1740 = quals_to_string' quals in
      let uu____1741 =
        let uu____1742 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1757 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1758 =
                    let uu____1759 = FStar_Options.print_universes () in
                    if uu____1759
                    then
                      let uu____1760 =
                        let uu____1761 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1761 ">" in
                      Prims.strcat "<" uu____1760
                    else "" in
                  let uu____1763 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1764 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1757 uu____1758
                    uu____1763 uu____1764)) in
        FStar_Util.concat_l "\n and " uu____1742 in
      FStar_Util.format3 "%slet %s %s" uu____1740
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1741
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1771 = FStar_Options.print_effect_args () in
    if uu____1771
    then
      let uu____1772 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1772
    else
      (let uu____1774 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1775 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1774 uu____1775)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___116_1777  ->
      match uu___116_1777 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1780 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1785 =
        let uu____1786 = FStar_Options.ugly () in
        Prims.op_Negation uu____1786 in
      if uu____1785
      then
        let uu____1787 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1787 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1793 = b in
         match uu____1793 with
         | (a,imp) ->
             let uu____1796 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1796
             then
               let uu____1797 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1797
             else
               (let uu____1799 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1801 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1801) in
                if uu____1799
                then
                  let uu____1802 = nm_to_string a in
                  imp_to_string uu____1802 imp
                else
                  (let uu____1804 =
                     let uu____1805 = nm_to_string a in
                     let uu____1806 =
                       let uu____1807 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1807 in
                     Prims.strcat uu____1805 uu____1806 in
                   imp_to_string uu____1804 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1813 = FStar_Options.print_implicits () in
        if uu____1813 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1815 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1815 (FStar_String.concat sep)
      else
        (let uu____1823 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1823 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___117_1830  ->
    match uu___117_1830 with
    | (a,imp) ->
        let uu____1843 = term_to_string a in imp_to_string uu____1843 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1846 = FStar_Options.print_implicits () in
      if uu____1846 then args else filter_imp args in
    let uu____1850 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1850 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1864 =
      let uu____1865 = FStar_Options.ugly () in Prims.op_Negation uu____1865 in
    if uu____1864
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1879 =
             let uu____1880 = FStar_Syntax_Subst.compress t in
             uu____1880.FStar_Syntax_Syntax.n in
           (match uu____1879 with
            | FStar_Syntax_Syntax.Tm_type uu____1883 when
                let uu____1884 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1884 -> term_to_string t
            | uu____1885 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1887 = univ_to_string u in
                     let uu____1888 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1887 uu____1888
                 | uu____1889 ->
                     let uu____1892 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1892))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1903 =
             let uu____1904 = FStar_Syntax_Subst.compress t in
             uu____1904.FStar_Syntax_Syntax.n in
           (match uu____1903 with
            | FStar_Syntax_Syntax.Tm_type uu____1907 when
                let uu____1908 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1908 -> term_to_string t
            | uu____1909 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1911 = univ_to_string u in
                     let uu____1912 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1911 uu____1912
                 | uu____1913 ->
                     let uu____1916 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1916))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1919 = FStar_Options.print_effect_args () in
             if uu____1919
             then
               let uu____1920 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1921 =
                 let uu____1922 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1922 (FStar_String.concat ", ") in
               let uu____1929 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1930 =
                 let uu____1931 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1931 (FStar_String.concat ", ") in
               let uu____1952 =
                 let uu____1953 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1953 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1920
                 uu____1921 uu____1929 uu____1930 uu____1952
             else
               (let uu____1963 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___118_1967  ->
                           match uu___118_1967 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1968 -> false)))
                    &&
                    (let uu____1970 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1970) in
                if uu____1963
                then
                  let uu____1971 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1971
                else
                  (let uu____1973 =
                     ((let uu____1976 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1976) &&
                        (let uu____1978 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1978))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____1973
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1980 =
                        (let uu____1983 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1983) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___119_1987  ->
                                   match uu___119_1987 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1988 -> false))) in
                      if uu____1980
                      then
                        let uu____1989 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1989
                      else
                        (let uu____1991 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1992 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1991 uu____1992)))) in
           let dec =
             let uu____1994 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___120_2004  ->
                       match uu___120_2004 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2010 =
                             let uu____2011 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2011 in
                           [uu____2010]
                       | uu____2012 -> [])) in
             FStar_All.pipe_right uu____1994 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2016 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2025 = b in
    match uu____2025 with
    | (a,imp) ->
        let n1 =
          let uu____2029 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2029
          then FStar_Util.JsonNull
          else
            (let uu____2031 =
               let uu____2032 = nm_to_string a in
               imp_to_string uu____2032 imp in
             FStar_Util.JsonStr uu____2031) in
        let t =
          let uu____2034 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2034 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2050 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2050
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2056 = FStar_Options.print_universes () in
    if uu____2056 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2061 =
      let uu____2062 = FStar_Options.ugly () in Prims.op_Negation uu____2062 in
    if uu____2061
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2066 = s in
       match uu____2066 with
       | (us,t) ->
           let uu____2073 =
             let uu____2074 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2074 in
           let uu____2075 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2073 uu____2075)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2079 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2080 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2081 =
      let uu____2082 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2082 in
    let uu____2083 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2084 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2079 uu____2080 uu____2081
      uu____2083 uu____2084
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
          let uu____2101 =
            let uu____2102 = FStar_Options.ugly () in
            Prims.op_Negation uu____2102 in
          if uu____2101
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2114 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2114 (FStar_String.concat ",\n\t") in
             let uu____2123 =
               let uu____2126 =
                 let uu____2129 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2130 =
                   let uu____2133 =
                     let uu____2134 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2134 in
                   let uu____2135 =
                     let uu____2138 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2139 =
                       let uu____2142 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2143 =
                         let uu____2146 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2147 =
                           let uu____2150 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2151 =
                             let uu____2154 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2155 =
                               let uu____2158 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2159 =
                                 let uu____2162 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2163 =
                                   let uu____2166 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2167 =
                                     let uu____2170 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2171 =
                                       let uu____2174 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2175 =
                                         let uu____2178 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2179 =
                                           let uu____2182 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2183 =
                                             let uu____2186 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2187 =
                                               let uu____2190 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2191 =
                                                 let uu____2194 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2195 =
                                                   let uu____2198 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2198] in
                                                 uu____2194 :: uu____2195 in
                                               uu____2190 :: uu____2191 in
                                             uu____2186 :: uu____2187 in
                                           uu____2182 :: uu____2183 in
                                         uu____2178 :: uu____2179 in
                                       uu____2174 :: uu____2175 in
                                     uu____2170 :: uu____2171 in
                                   uu____2166 :: uu____2167 in
                                 uu____2162 :: uu____2163 in
                               uu____2158 :: uu____2159 in
                             uu____2154 :: uu____2155 in
                           uu____2150 :: uu____2151 in
                         uu____2146 :: uu____2147 in
                       uu____2142 :: uu____2143 in
                     uu____2138 :: uu____2139 in
                   uu____2133 :: uu____2135 in
                 uu____2129 :: uu____2130 in
               (if for_free then "_for_free " else "") :: uu____2126 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2123)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2209 =
      let uu____2210 = FStar_Options.ugly () in Prims.op_Negation uu____2210 in
    if uu____2209
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2216 -> ""
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
           (lid,univs1,tps,k,uu____2226,uu____2227) ->
           let uu____2236 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____2237 = binders_to_string " " tps in
           let uu____2238 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____2236
             lid.FStar_Ident.str uu____2237 uu____2238
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____2242,uu____2243,uu____2244) ->
           let uu____2249 = FStar_Options.print_universes () in
           if uu____2249
           then
             let uu____2250 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2250 with
              | (univs2,t1) ->
                  let uu____2257 = univ_names_to_string univs2 in
                  let uu____2258 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____2257
                    lid.FStar_Ident.str uu____2258)
           else
             (let uu____2260 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____2260)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____2264 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____2264 with
            | (univs2,t1) ->
                let uu____2271 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____2272 =
                  let uu____2273 = FStar_Options.print_universes () in
                  if uu____2273
                  then
                    let uu____2274 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____2274
                  else "" in
                let uu____2276 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____2271
                  lid.FStar_Ident.str uu____2272 uu____2276)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____2278,f) ->
           let uu____2280 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2280
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2282) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____2288 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____2288
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2290) ->
           let uu____2299 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____2299 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____2317) -> lift_wp
             | (uu____2324,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____2332 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____2332 with
            | (us,t) ->
                let uu____2343 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____2344 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____2345 = univ_names_to_string us in
                let uu____2346 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____2343
                  uu____2344 uu____2345 uu____2346)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____2356 = FStar_Options.print_universes () in
           if uu____2356
           then
             let uu____2357 =
               let uu____2362 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____2362 in
             (match uu____2357 with
              | (univs2,t) ->
                  let uu____2365 =
                    let uu____2378 =
                      let uu____2379 = FStar_Syntax_Subst.compress t in
                      uu____2379.FStar_Syntax_Syntax.n in
                    match uu____2378 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____2420 -> failwith "impossible" in
                  (match uu____2365 with
                   | (tps1,c1) ->
                       let uu____2451 = sli l in
                       let uu____2452 = univ_names_to_string univs2 in
                       let uu____2453 = binders_to_string " " tps1 in
                       let uu____2454 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____2451
                         uu____2452 uu____2453 uu____2454))
           else
             (let uu____2456 = sli l in
              let uu____2457 = binders_to_string " " tps in
              let uu____2458 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____2456 uu____2457
                uu____2458))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2465 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2465 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2469,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2471;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2473;
                       FStar_Syntax_Syntax.lbdef = uu____2474;_}::[]),uu____2475)
        ->
        let uu____2498 = lbname_to_string lb in
        let uu____2499 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2498 uu____2499
    | uu____2500 ->
        let uu____2501 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2501 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2515 = sli m.FStar_Syntax_Syntax.name in
    let uu____2516 =
      let uu____2517 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2517 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2515 uu____2516
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___121_2524  ->
    match uu___121_2524 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2527 = FStar_Util.string_of_int i in
        let uu____2528 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2527 uu____2528
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2531 = bv_to_string x in
        let uu____2532 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2531 uu____2532
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2539 = bv_to_string x in
        let uu____2540 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2539 uu____2540
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2543 = FStar_Util.string_of_int i in
        let uu____2544 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2543 uu____2544
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2547 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2547
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2551 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2551 (FStar_String.concat "; ")
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
           (let uu____2619 = f x in
            FStar_Util.string_builder_append strb uu____2619);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2626 = f x1 in
                 FStar_Util.string_builder_append strb uu____2626)) xs;
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
           (let uu____2659 = f x in
            FStar_Util.string_builder_append strb uu____2659);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2666 = f x1 in
                 FStar_Util.string_builder_append strb uu____2666)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)