
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
             let uu____1320 =
               let uu____1321 = term_to_string x3.FStar_Syntax_Syntax.sort in
               Prims.strcat uu____1321 ")" in
             Prims.strcat ":(" uu____1320 in
           Prims.strcat uu____1318 uu____1319
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1325) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1352 = FStar_Options.print_universes () in
           if uu____1352
           then
             let uu____1353 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1353
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1373 = binders_to_string " -> " bs in
           let uu____1374 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1373 uu____1374
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1399 = binders_to_string " " bs in
                let uu____1400 = term_to_string t2 in
                let uu____1401 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1405 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1405) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1399 uu____1400
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1401
            | uu____1408 ->
                let uu____1411 = binders_to_string " " bs in
                let uu____1412 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1411 uu____1412)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1419 = bv_to_string xt in
           let uu____1420 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1423 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1419 uu____1420 uu____1423
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1448 = term_to_string t in
           let uu____1449 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1448 uu____1449
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1468 = lbs_to_string [] lbs in
           let uu____1469 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1468 uu____1469
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1530 =
                   let uu____1531 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1531
                     (FStar_Util.dflt "default") in
                 let uu____1536 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1530 uu____1536
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1552 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1552 in
           let uu____1553 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1553 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1592 = term_to_string head1 in
           let uu____1593 =
             let uu____1594 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1630  ->
                       match uu____1630 with
                       | (p,wopt,e) ->
                           let uu____1646 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1647 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1649 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1649 in
                           let uu____1650 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1646
                             uu____1647 uu____1650)) in
             FStar_Util.concat_l "\n\t|" uu____1594 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1592 uu____1593
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1657 = FStar_Options.print_universes () in
           if uu____1657
           then
             let uu____1658 = term_to_string t in
             let uu____1659 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1658 uu____1659
           else term_to_string t
       | uu____1661 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1663 =
      let uu____1664 = FStar_Options.ugly () in Prims.op_Negation uu____1664 in
    if uu____1663
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1686 = fv_to_string l in
           let uu____1687 =
             let uu____1688 =
               FStar_List.map
                 (fun uu____1699  ->
                    match uu____1699 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1688 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1686 uu____1687
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1711) ->
           let uu____1716 = FStar_Options.print_bound_var_types () in
           if uu____1716
           then
             let uu____1717 = bv_to_string x1 in
             let uu____1718 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1717 uu____1718
           else
             (let uu____1720 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1720)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1722 = FStar_Options.print_bound_var_types () in
           if uu____1722
           then
             let uu____1723 = bv_to_string x1 in
             let uu____1724 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1723 uu____1724
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1728 = FStar_Options.print_real_names () in
           if uu____1728
           then
             let uu____1729 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1729
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1741 = quals_to_string' quals in
      let uu____1742 =
        let uu____1743 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1758 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1759 =
                    let uu____1760 = FStar_Options.print_universes () in
                    if uu____1760
                    then
                      let uu____1761 =
                        let uu____1762 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1762 ">" in
                      Prims.strcat "<" uu____1761
                    else "" in
                  let uu____1764 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1765 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1758 uu____1759
                    uu____1764 uu____1765)) in
        FStar_Util.concat_l "\n and " uu____1743 in
      FStar_Util.format3 "%slet %s %s" uu____1741
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1742
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1772 = FStar_Options.print_effect_args () in
    if uu____1772
    then
      let uu____1773 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1773
    else
      (let uu____1775 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1776 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1775 uu____1776)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___116_1778  ->
      match uu___116_1778 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1781 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1786 =
        let uu____1787 = FStar_Options.ugly () in
        Prims.op_Negation uu____1787 in
      if uu____1786
      then
        let uu____1788 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1788 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1794 = b in
         match uu____1794 with
         | (a,imp) ->
             let uu____1797 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1797
             then
               let uu____1798 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1798
             else
               (let uu____1800 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1802 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1802) in
                if uu____1800
                then
                  let uu____1803 = nm_to_string a in
                  imp_to_string uu____1803 imp
                else
                  (let uu____1805 =
                     let uu____1806 = nm_to_string a in
                     let uu____1807 =
                       let uu____1808 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1808 in
                     Prims.strcat uu____1806 uu____1807 in
                   imp_to_string uu____1805 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1814 = FStar_Options.print_implicits () in
        if uu____1814 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1816 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1816 (FStar_String.concat sep)
      else
        (let uu____1824 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1824 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___117_1831  ->
    match uu___117_1831 with
    | (a,imp) ->
        let uu____1844 = term_to_string a in imp_to_string uu____1844 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1847 = FStar_Options.print_implicits () in
      if uu____1847 then args else filter_imp args in
    let uu____1851 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1851 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1865 =
      let uu____1866 = FStar_Options.ugly () in Prims.op_Negation uu____1866 in
    if uu____1865
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1880 =
             let uu____1881 = FStar_Syntax_Subst.compress t in
             uu____1881.FStar_Syntax_Syntax.n in
           (match uu____1880 with
            | FStar_Syntax_Syntax.Tm_type uu____1884 when
                let uu____1885 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1885 -> term_to_string t
            | uu____1886 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1888 = univ_to_string u in
                     let uu____1889 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1888 uu____1889
                 | uu____1890 ->
                     let uu____1893 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1893))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1904 =
             let uu____1905 = FStar_Syntax_Subst.compress t in
             uu____1905.FStar_Syntax_Syntax.n in
           (match uu____1904 with
            | FStar_Syntax_Syntax.Tm_type uu____1908 when
                let uu____1909 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1909 -> term_to_string t
            | uu____1910 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1912 = univ_to_string u in
                     let uu____1913 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1912 uu____1913
                 | uu____1914 ->
                     let uu____1917 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1917))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1920 = FStar_Options.print_effect_args () in
             if uu____1920
             then
               let uu____1921 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1922 =
                 let uu____1923 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1923 (FStar_String.concat ", ") in
               let uu____1930 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1931 =
                 let uu____1932 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1932 (FStar_String.concat ", ") in
               let uu____1953 =
                 let uu____1954 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1954 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1921
                 uu____1922 uu____1930 uu____1931 uu____1953
             else
               (let uu____1964 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___118_1968  ->
                           match uu___118_1968 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1969 -> false)))
                    &&
                    (let uu____1971 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1971) in
                if uu____1964
                then
                  let uu____1972 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1972
                else
                  (let uu____1974 =
                     ((let uu____1977 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1977) &&
                        (let uu____1979 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1979))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____1974
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1981 =
                        (let uu____1984 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1984) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___119_1988  ->
                                   match uu___119_1988 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1989 -> false))) in
                      if uu____1981
                      then
                        let uu____1990 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1990
                      else
                        (let uu____1992 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1993 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1992 uu____1993)))) in
           let dec =
             let uu____1995 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___120_2005  ->
                       match uu___120_2005 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2011 =
                             let uu____2012 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2012 in
                           [uu____2011]
                       | uu____2013 -> [])) in
             FStar_All.pipe_right uu____1995 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2017 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2026 = b in
    match uu____2026 with
    | (a,imp) ->
        let n1 =
          let uu____2030 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2030
          then FStar_Util.JsonNull
          else
            (let uu____2032 =
               let uu____2033 = nm_to_string a in
               imp_to_string uu____2033 imp in
             FStar_Util.JsonStr uu____2032) in
        let t =
          let uu____2035 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2035 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2051 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2051
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2057 = FStar_Options.print_universes () in
    if uu____2057 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2062 =
      let uu____2063 = FStar_Options.ugly () in Prims.op_Negation uu____2063 in
    if uu____2062
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2067 = s in
       match uu____2067 with
       | (us,t) ->
           let uu____2074 =
             let uu____2075 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2075 in
           let uu____2076 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2074 uu____2076)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2080 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2081 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2082 =
      let uu____2083 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2083 in
    let uu____2084 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2085 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2080 uu____2081 uu____2082
      uu____2084 uu____2085
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
          let uu____2102 =
            let uu____2103 = FStar_Options.ugly () in
            Prims.op_Negation uu____2103 in
          if uu____2102
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2115 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2115 (FStar_String.concat ",\n\t") in
             let uu____2124 =
               let uu____2127 =
                 let uu____2130 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2131 =
                   let uu____2134 =
                     let uu____2135 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2135 in
                   let uu____2136 =
                     let uu____2139 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2140 =
                       let uu____2143 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2144 =
                         let uu____2147 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2148 =
                           let uu____2151 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2152 =
                             let uu____2155 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2156 =
                               let uu____2159 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2160 =
                                 let uu____2163 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2164 =
                                   let uu____2167 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2168 =
                                     let uu____2171 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2172 =
                                       let uu____2175 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2176 =
                                         let uu____2179 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2180 =
                                           let uu____2183 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2184 =
                                             let uu____2187 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2188 =
                                               let uu____2191 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2192 =
                                                 let uu____2195 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2196 =
                                                   let uu____2199 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2199] in
                                                 uu____2195 :: uu____2196 in
                                               uu____2191 :: uu____2192 in
                                             uu____2187 :: uu____2188 in
                                           uu____2183 :: uu____2184 in
                                         uu____2179 :: uu____2180 in
                                       uu____2175 :: uu____2176 in
                                     uu____2171 :: uu____2172 in
                                   uu____2167 :: uu____2168 in
                                 uu____2163 :: uu____2164 in
                               uu____2159 :: uu____2160 in
                             uu____2155 :: uu____2156 in
                           uu____2151 :: uu____2152 in
                         uu____2147 :: uu____2148 in
                       uu____2143 :: uu____2144 in
                     uu____2139 :: uu____2140 in
                   uu____2134 :: uu____2136 in
                 uu____2130 :: uu____2131 in
               (if for_free then "_for_free " else "") :: uu____2127 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2124)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2210 =
      let uu____2211 = FStar_Options.ugly () in Prims.op_Negation uu____2211 in
    if uu____2210
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2217 -> ""
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
             (lid,univs1,tps,k,uu____2228,uu____2229) ->
             let uu____2238 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let uu____2239 = binders_to_string " " tps in
             let uu____2240 = term_to_string k in
             FStar_Util.format4 "%stype %s %s : %s" uu____2238
               lid.FStar_Ident.str uu____2239 uu____2240
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2244,uu____2245,uu____2246) ->
             let uu____2251 = FStar_Options.print_universes () in
             if uu____2251
             then
               let uu____2252 = univ_names_to_string univs1 in
               let uu____2253 = term_to_string t in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2252
                 lid.FStar_Ident.str uu____2253
             else
               (let uu____2255 = term_to_string t in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2255)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2259 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2259 with
              | (univs2,t1) ->
                  let uu____2266 =
                    quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                  let uu____2267 =
                    let uu____2268 = FStar_Options.print_universes () in
                    if uu____2268
                    then
                      let uu____2269 = univ_names_to_string univs2 in
                      FStar_Util.format1 "<%s>" uu____2269
                    else "" in
                  let uu____2271 = term_to_string t1 in
                  FStar_Util.format4 "%sval %s %s : %s" uu____2266
                    lid.FStar_Ident.str uu____2267 uu____2271)
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2273,f) ->
             let uu____2275 = term_to_string f in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2275
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2277) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2283 = term_to_string e in
             FStar_Util.format1 "let _ = %s" uu____2283
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2285) ->
             let uu____2294 = FStar_List.map sigelt_to_string ses in
             FStar_All.pipe_right uu____2294 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2312) -> lift_wp
               | (uu____2319,FStar_Pervasives_Native.Some lift) -> lift in
             let uu____2327 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp) in
             (match uu____2327 with
              | (us,t) ->
                  let uu____2338 =
                    lid_to_string se.FStar_Syntax_Syntax.source in
                  let uu____2339 =
                    lid_to_string se.FStar_Syntax_Syntax.target in
                  let uu____2340 = univ_names_to_string us in
                  let uu____2341 = term_to_string t in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2338 uu____2339 uu____2340 uu____2341)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
             let uu____2351 = FStar_Options.print_universes () in
             if uu____2351
             then
               let uu____2352 =
                 let uu____2357 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2357 in
               (match uu____2352 with
                | (univs2,t) ->
                    let uu____2360 =
                      let uu____2373 =
                        let uu____2374 = FStar_Syntax_Subst.compress t in
                        uu____2374.FStar_Syntax_Syntax.n in
                      match uu____2373 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2415 -> failwith "impossible" in
                    (match uu____2360 with
                     | (tps1,c1) ->
                         let uu____2446 = sli l in
                         let uu____2447 = univ_names_to_string univs2 in
                         let uu____2448 = binders_to_string " " tps1 in
                         let uu____2449 = comp_to_string c1 in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2446 uu____2447 uu____2448 uu____2449))
             else
               (let uu____2451 = sli l in
                let uu____2452 = binders_to_string " " tps in
                let uu____2453 = comp_to_string c in
                FStar_Util.format3 "effect %s %s = %s" uu____2451 uu____2452
                  uu____2453) in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2454 ->
           let attrs =
             FStar_All.pipe_right x.FStar_Syntax_Syntax.sigattrs
               (FStar_List.map term_to_string) in
           let uu____2464 =
             FStar_All.pipe_right attrs (FStar_String.concat " ") in
           FStar_Util.format2 "[@%s]\n%s" uu____2464 basic)
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2473 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2473 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2477,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2479;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2481;
                       FStar_Syntax_Syntax.lbdef = uu____2482;_}::[]),uu____2483)
        ->
        let uu____2506 = lbname_to_string lb in
        let uu____2507 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2506 uu____2507
    | uu____2508 ->
        let uu____2509 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2509 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2523 = sli m.FStar_Syntax_Syntax.name in
    let uu____2524 =
      let uu____2525 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2525 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2523 uu____2524
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___121_2532  ->
    match uu___121_2532 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2535 = FStar_Util.string_of_int i in
        let uu____2536 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2535 uu____2536
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2539 = bv_to_string x in
        let uu____2540 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2539 uu____2540
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2547 = bv_to_string x in
        let uu____2548 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2547 uu____2548
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2551 = FStar_Util.string_of_int i in
        let uu____2552 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2551 uu____2552
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2555 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2555
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2559 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2559 (FStar_String.concat "; ")
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
           (let uu____2627 = f x in
            FStar_Util.string_builder_append strb uu____2627);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2634 = f x1 in
                 FStar_Util.string_builder_append strb uu____2634)) xs;
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
           (let uu____2667 = f x in
            FStar_Util.string_builder_append strb uu____2667);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2674 = f x1 in
                 FStar_Util.string_builder_append strb uu____2674)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)