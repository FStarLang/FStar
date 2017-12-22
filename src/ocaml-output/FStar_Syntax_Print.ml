open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___62_3  ->
    match uu___62_3 with
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
  fun uu___63_241  ->
    match uu___63_241 with
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
         (fun uu___64_304  ->
            match uu___64_304 with
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
  fun uu___65_567  ->
    match uu___65_567 with
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
         | FStar_Pervasives_Native.Some uu____847 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____852 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____862 = FStar_Options.hide_uvar_nums () in
    if uu____862
    then "?"
    else
      (let uu____864 =
         let uu____865 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____865 FStar_Util.string_of_int in
       Prims.strcat "?" uu____864)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____869 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____870 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____869 uu____870
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____874 = FStar_Options.hide_uvar_nums () in
    if uu____874
    then "?"
    else
      (let uu____876 =
         let uu____877 =
           let uu____878 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____878 FStar_Util.string_of_int in
         let uu____879 =
           let uu____880 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____880 in
         Prims.strcat uu____877 uu____879 in
       Prims.strcat "?" uu____876)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____897 = FStar_Syntax_Subst.compress_univ u in
      match uu____897 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____907 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____913 =
      let uu____914 = FStar_Options.ugly () in Prims.op_Negation uu____914 in
    if uu____913
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____918 = FStar_Syntax_Subst.compress_univ u in
       match uu____918 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____930 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____930
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____932 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____932 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____946 = univ_to_string u2 in
                let uu____947 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____946 uu____947)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____951 =
             let uu____952 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____952 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____951
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____964 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____964 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____976 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____976 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___66_985  ->
    match uu___66_985 with
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
        let uu____987 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____987
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____990 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____990 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____1001 =
          let uu____1002 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1002 in
        let uu____1005 =
          let uu____1006 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1006 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____1001 uu____1005
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____1025 =
          let uu____1026 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____1026 in
        let uu____1029 =
          let uu____1030 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____1030 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____1025 uu____1029
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____1040 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____1040
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
    | uu____1049 ->
        let uu____1052 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____1052 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____1068 ->
        let uu____1071 = quals_to_string quals in Prims.strcat uu____1071 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____1127 =
      let uu____1128 = FStar_Options.ugly () in Prims.op_Negation uu____1128 in
    if uu____1127
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____1134 = FStar_Options.print_implicits () in
         if uu____1134 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____1136 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____1161,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____1197 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____1227 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____1245  ->
                                 match uu____1245 with
                                 | (t1,uu____1251) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____1227
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____1197 (FStar_String.concat "\\/") in
           let uu____1256 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____1256
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____1268 = tag_of_term t in
           let uu____1269 = sli m in
           let uu____1270 = term_to_string t' in
           let uu____1271 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____1268 uu____1269
             uu____1270 uu____1271
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____1284 = tag_of_term t in
           let uu____1285 = term_to_string t' in
           let uu____1286 = sli m0 in
           let uu____1287 = sli m1 in
           let uu____1288 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____1284
             uu____1285 uu____1286 uu____1287 uu____1288
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____1290,s,uu____1292)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) ->
           let uu____1309 = FStar_Range.string_of_range r in
           let uu____1310 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____1309
             uu____1310
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_named l) ->
           let uu____1317 = lid_to_string l in
           let uu____1318 =
             FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos in
           let uu____1319 = term_to_string t in
           FStar_Util.format3 "Meta_named(%s, %s){%s}" uu____1317 uu____1318
             uu____1319
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_desugared uu____1321) ->
           let uu____1326 = term_to_string t in
           FStar_Util.format1 "Meta_desugared{%s}" uu____1326
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1328 = db_to_string x3 in
           let uu____1329 =
             let uu____1330 =
               let uu____1331 = tag_of_term x3.FStar_Syntax_Syntax.sort in
               Prims.strcat uu____1331 ")" in
             Prims.strcat ":(" uu____1330 in
           Prims.strcat uu____1328 uu____1329
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1335) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1362 = FStar_Options.print_universes () in
           if uu____1362
           then
             let uu____1363 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1363
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1383 = binders_to_string " -> " bs in
           let uu____1384 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1383 uu____1384
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1409 = binders_to_string " " bs in
                let uu____1410 = term_to_string t2 in
                let uu____1411 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1415 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1415) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1409 uu____1410
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1411
            | uu____1418 ->
                let uu____1421 = binders_to_string " " bs in
                let uu____1422 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1421 uu____1422)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1429 = bv_to_string xt in
           let uu____1430 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1433 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1429 uu____1430 uu____1433
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1458 = term_to_string t in
           let uu____1459 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1458 uu____1459
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1478 = lbs_to_string [] lbs in
           let uu____1479 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1478 uu____1479
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1540 =
                   let uu____1541 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1541
                     (FStar_Util.dflt "default") in
                 let uu____1546 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1540 uu____1546
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1562 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1562 in
           let uu____1563 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1563 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1602 = term_to_string head1 in
           let uu____1603 =
             let uu____1604 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1640  ->
                       match uu____1640 with
                       | (p,wopt,e) ->
                           let uu____1656 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1657 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1659 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1659 in
                           let uu____1660 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1656
                             uu____1657 uu____1660)) in
             FStar_Util.concat_l "\n\t|" uu____1604 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1602 uu____1603
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1667 = FStar_Options.print_universes () in
           if uu____1667
           then
             let uu____1668 = term_to_string t in
             let uu____1669 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1668 uu____1669
           else term_to_string t
       | uu____1671 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1673 =
      let uu____1674 = FStar_Options.ugly () in Prims.op_Negation uu____1674 in
    if uu____1673
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1696 = fv_to_string l in
           let uu____1697 =
             let uu____1698 =
               FStar_List.map
                 (fun uu____1709  ->
                    match uu____1709 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1698 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1696 uu____1697
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1721) ->
           let uu____1726 = FStar_Options.print_bound_var_types () in
           if uu____1726
           then
             let uu____1727 = bv_to_string x1 in
             let uu____1728 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1727 uu____1728
           else
             (let uu____1730 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1730)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1732 = FStar_Options.print_bound_var_types () in
           if uu____1732
           then
             let uu____1733 = bv_to_string x1 in
             let uu____1734 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1733 uu____1734
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1738 = FStar_Options.print_real_names () in
           if uu____1738
           then
             let uu____1739 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1739
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let uu____1751 = quals_to_string' quals in
      let uu____1752 =
        let uu____1753 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
            (FStar_List.map
               (fun lb  ->
                  let uu____1768 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1769 =
                    let uu____1770 = FStar_Options.print_universes () in
                    if uu____1770
                    then
                      let uu____1771 =
                        let uu____1772 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1772 ">" in
                      Prims.strcat "<" uu____1771
                    else "" in
                  let uu____1774 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1775 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1768 uu____1769
                    uu____1774 uu____1775)) in
        FStar_Util.concat_l "\n and " uu____1753 in
      FStar_Util.format3 "%slet %s %s" uu____1751
        (if FStar_Pervasives_Native.fst lbs then "rec" else "") uu____1752
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1782 = FStar_Options.print_effect_args () in
    if uu____1782
    then
      let uu____1783 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1783
    else
      (let uu____1785 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1786 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1785 uu____1786)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___67_1788  ->
      match uu___67_1788 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1791 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1796 =
        let uu____1797 = FStar_Options.ugly () in
        Prims.op_Negation uu____1797 in
      if uu____1796
      then
        let uu____1798 =
          FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        match uu____1798 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some e ->
            let d = FStar_Parser_ToDocument.binder_to_document e in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d
      else
        (let uu____1804 = b in
         match uu____1804 with
         | (a,imp) ->
             let uu____1807 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1807
             then
               let uu____1808 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1808
             else
               (let uu____1810 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1812 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1812) in
                if uu____1810
                then
                  let uu____1813 = nm_to_string a in
                  imp_to_string uu____1813 imp
                else
                  (let uu____1815 =
                     let uu____1816 = nm_to_string a in
                     let uu____1817 =
                       let uu____1818 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1818 in
                     Prims.strcat uu____1816 uu____1817 in
                   imp_to_string uu____1815 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1824 = FStar_Options.print_implicits () in
        if uu____1824 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1826 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1826 (FStar_String.concat sep)
      else
        (let uu____1834 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1834 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___68_1841  ->
    match uu___68_1841 with
    | (a,imp) ->
        let uu____1854 = term_to_string a in imp_to_string uu____1854 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1857 = FStar_Options.print_implicits () in
      if uu____1857 then args else filter_imp args in
    let uu____1861 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1861 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1875 =
      let uu____1876 = FStar_Options.ugly () in Prims.op_Negation uu____1876 in
    if uu____1875
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1890 =
             let uu____1891 = FStar_Syntax_Subst.compress t in
             uu____1891.FStar_Syntax_Syntax.n in
           (match uu____1890 with
            | FStar_Syntax_Syntax.Tm_type uu____1894 when
                let uu____1895 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1895 -> term_to_string t
            | uu____1896 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1898 = univ_to_string u in
                     let uu____1899 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1898 uu____1899
                 | uu____1900 ->
                     let uu____1903 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1903))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1914 =
             let uu____1915 = FStar_Syntax_Subst.compress t in
             uu____1915.FStar_Syntax_Syntax.n in
           (match uu____1914 with
            | FStar_Syntax_Syntax.Tm_type uu____1918 when
                let uu____1919 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1919 -> term_to_string t
            | uu____1920 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1922 = univ_to_string u in
                     let uu____1923 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1922 uu____1923
                 | uu____1924 ->
                     let uu____1927 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1927))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1930 = FStar_Options.print_effect_args () in
             if uu____1930
             then
               let uu____1931 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1932 =
                 let uu____1933 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1933 (FStar_String.concat ", ") in
               let uu____1940 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1941 =
                 let uu____1942 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1942 (FStar_String.concat ", ") in
               let uu____1963 =
                 let uu____1964 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1964 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1931
                 uu____1932 uu____1940 uu____1941 uu____1963
             else
               (let uu____1974 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___69_1978  ->
                           match uu___69_1978 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1979 -> false)))
                    &&
                    (let uu____1981 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1981) in
                if uu____1974
                then
                  let uu____1982 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1982
                else
                  (let uu____1984 =
                     ((let uu____1987 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1987) &&
                        (let uu____1989 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1989))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____1984
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1991 =
                        (let uu____1994 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1994) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___70_1998  ->
                                   match uu___70_1998 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1999 -> false))) in
                      if uu____1991
                      then
                        let uu____2000 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____2000
                      else
                        (let uu____2002 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____2003 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____2002 uu____2003)))) in
           let dec =
             let uu____2005 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___71_2015  ->
                       match uu___71_2015 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____2021 =
                             let uu____2022 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____2022 in
                           [uu____2021]
                       | uu____2023 -> [])) in
             FStar_All.pipe_right uu____2005 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____2027 -> ""
and formula_to_string:
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.string =
  fun phi  -> term_to_string phi
let binder_to_json: FStar_Syntax_Syntax.binder -> FStar_Util.json =
  fun b  ->
    let uu____2036 = b in
    match uu____2036 with
    | (a,imp) ->
        let n1 =
          let uu____2040 = FStar_Syntax_Syntax.is_null_binder b in
          if uu____2040
          then FStar_Util.JsonNull
          else
            (let uu____2042 =
               let uu____2043 = nm_to_string a in
               imp_to_string uu____2043 imp in
             FStar_Util.JsonStr uu____2042) in
        let t =
          let uu____2045 = term_to_string a.FStar_Syntax_Syntax.sort in
          FStar_Util.JsonStr uu____2045 in
        FStar_Util.JsonAssoc [("name", n1); ("type", t)]
let binders_to_json: FStar_Syntax_Syntax.binders -> FStar_Util.json =
  fun bs  ->
    let uu____2061 = FStar_List.map binder_to_json bs in
    FStar_Util.JsonList uu____2061
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____2067 = FStar_Options.print_universes () in
    if uu____2067 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____2072 =
      let uu____2073 = FStar_Options.ugly () in Prims.op_Negation uu____2073 in
    if uu____2072
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____2077 = s in
       match uu____2077 with
       | (us,t) ->
           let uu____2084 =
             let uu____2085 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____2085 in
           let uu____2086 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____2084 uu____2086)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____2090 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____2091 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____2092 =
      let uu____2093 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____2093 in
    let uu____2094 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____2095 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____2090 uu____2091 uu____2092
      uu____2094 uu____2095
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
          let uu____2112 =
            let uu____2113 = FStar_Options.ugly () in
            Prims.op_Negation uu____2113 in
          if uu____2112
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____2125 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____2125 (FStar_String.concat ",\n\t") in
             let uu____2134 =
               let uu____2137 =
                 let uu____2140 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____2141 =
                   let uu____2144 =
                     let uu____2145 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____2145 in
                   let uu____2146 =
                     let uu____2149 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____2150 =
                       let uu____2153 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____2154 =
                         let uu____2157 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____2158 =
                           let uu____2161 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____2162 =
                             let uu____2165 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____2166 =
                               let uu____2169 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____2170 =
                                 let uu____2173 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____2174 =
                                   let uu____2177 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____2178 =
                                     let uu____2181 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____2182 =
                                       let uu____2185 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____2186 =
                                         let uu____2189 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____2190 =
                                           let uu____2193 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____2194 =
                                             let uu____2197 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____2198 =
                                               let uu____2201 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____2202 =
                                                 let uu____2205 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____2206 =
                                                   let uu____2209 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____2209] in
                                                 uu____2205 :: uu____2206 in
                                               uu____2201 :: uu____2202 in
                                             uu____2197 :: uu____2198 in
                                           uu____2193 :: uu____2194 in
                                         uu____2189 :: uu____2190 in
                                       uu____2185 :: uu____2186 in
                                     uu____2181 :: uu____2182 in
                                   uu____2177 :: uu____2178 in
                                 uu____2173 :: uu____2174 in
                               uu____2169 :: uu____2170 in
                             uu____2165 :: uu____2166 in
                           uu____2161 :: uu____2162 in
                         uu____2157 :: uu____2158 in
                       uu____2153 :: uu____2154 in
                     uu____2149 :: uu____2150 in
                   uu____2144 :: uu____2146 in
                 uu____2140 :: uu____2141 in
               (if for_free then "_for_free " else "") :: uu____2137 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____2134)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____2220 =
      let uu____2221 = FStar_Options.ugly () in Prims.op_Negation uu____2221 in
    if uu____2220
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____2227 -> ""
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
             (lid,univs1,tps,k,uu____2238,uu____2239) ->
             let uu____2248 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
             let uu____2249 = binders_to_string " " tps in
             let uu____2250 = term_to_string k in
             FStar_Util.format4 "%stype %s %s : %s" uu____2248
               lid.FStar_Ident.str uu____2249 uu____2250
         | FStar_Syntax_Syntax.Sig_datacon
             (lid,univs1,t,uu____2254,uu____2255,uu____2256) ->
             let uu____2261 = FStar_Options.print_universes () in
             if uu____2261
             then
               let uu____2262 = univ_names_to_string univs1 in
               let uu____2263 = term_to_string t in
               FStar_Util.format3 "datacon<%s> %s : %s" uu____2262
                 lid.FStar_Ident.str uu____2263
             else
               (let uu____2265 = term_to_string t in
                FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                  uu____2265)
         | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
             let uu____2269 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____2269 with
              | (univs2,t1) ->
                  let uu____2276 =
                    quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                  let uu____2277 =
                    let uu____2278 = FStar_Options.print_universes () in
                    if uu____2278
                    then
                      let uu____2279 = univ_names_to_string univs2 in
                      FStar_Util.format1 "<%s>" uu____2279
                    else "" in
                  let uu____2281 = term_to_string t1 in
                  FStar_Util.format4 "%sval %s %s : %s" uu____2276
                    lid.FStar_Ident.str uu____2277 uu____2281)
         | FStar_Syntax_Syntax.Sig_assume (lid,uu____2283,f) ->
             let uu____2285 = term_to_string f in
             FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____2285
         | FStar_Syntax_Syntax.Sig_let (lbs,uu____2287) ->
             lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
         | FStar_Syntax_Syntax.Sig_main e ->
             let uu____2293 = term_to_string e in
             FStar_Util.format1 "let _ = %s" uu____2293
         | FStar_Syntax_Syntax.Sig_bundle (ses,uu____2295) ->
             let uu____2304 = FStar_List.map sigelt_to_string ses in
             FStar_All.pipe_right uu____2304 (FStar_String.concat "\n")
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
               | (FStar_Pervasives_Native.Some lift_wp,uu____2322) -> lift_wp
               | (uu____2329,FStar_Pervasives_Native.Some lift) -> lift in
             let uu____2337 =
               FStar_Syntax_Subst.open_univ_vars
                 (FStar_Pervasives_Native.fst lift_wp)
                 (FStar_Pervasives_Native.snd lift_wp) in
             (match uu____2337 with
              | (us,t) ->
                  let uu____2348 =
                    lid_to_string se.FStar_Syntax_Syntax.source in
                  let uu____2349 =
                    lid_to_string se.FStar_Syntax_Syntax.target in
                  let uu____2350 = univ_names_to_string us in
                  let uu____2351 = term_to_string t in
                  FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s"
                    uu____2348 uu____2349 uu____2350 uu____2351)
         | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags1) ->
             let uu____2361 = FStar_Options.print_universes () in
             if uu____2361
             then
               let uu____2362 =
                 let uu____2367 =
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                     FStar_Pervasives_Native.None FStar_Range.dummyRange in
                 FStar_Syntax_Subst.open_univ_vars univs1 uu____2367 in
               (match uu____2362 with
                | (univs2,t) ->
                    let uu____2370 =
                      let uu____2383 =
                        let uu____2384 = FStar_Syntax_Subst.compress t in
                        uu____2384.FStar_Syntax_Syntax.n in
                      match uu____2383 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                      | uu____2425 -> failwith "impossible" in
                    (match uu____2370 with
                     | (tps1,c1) ->
                         let uu____2456 = sli l in
                         let uu____2457 = univ_names_to_string univs2 in
                         let uu____2458 = binders_to_string " " tps1 in
                         let uu____2459 = comp_to_string c1 in
                         FStar_Util.format4 "effect %s<%s> %s = %s"
                           uu____2456 uu____2457 uu____2458 uu____2459))
             else
               (let uu____2461 = sli l in
                let uu____2462 = binders_to_string " " tps in
                let uu____2463 = comp_to_string c in
                FStar_Util.format3 "effect %s %s = %s" uu____2461 uu____2462
                  uu____2463) in
       match x.FStar_Syntax_Syntax.sigattrs with
       | [] -> basic
       | uu____2464 ->
           let attrs =
             FStar_All.pipe_right x.FStar_Syntax_Syntax.sigattrs
               (FStar_List.map term_to_string) in
           let uu____2474 =
             FStar_All.pipe_right attrs (FStar_String.concat " ") in
           FStar_Util.format2 "[@%s]\n%s" uu____2474 basic)
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____2483 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____2483 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____2487,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____2489;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____2491;
                       FStar_Syntax_Syntax.lbdef = uu____2492;_}::[]),uu____2493)
        ->
        let uu____2516 = lbname_to_string lb in
        let uu____2517 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2516 uu____2517
    | uu____2518 ->
        let uu____2519 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2519 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2533 = sli m.FStar_Syntax_Syntax.name in
    let uu____2534 =
      let uu____2535 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2535 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2533 uu____2534
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___72_2542  ->
    match uu___72_2542 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2545 = FStar_Util.string_of_int i in
        let uu____2546 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2545 uu____2546
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2549 = bv_to_string x in
        let uu____2550 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2549 uu____2550
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2557 = bv_to_string x in
        let uu____2558 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2557 uu____2558
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2561 = FStar_Util.string_of_int i in
        let uu____2562 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2561 uu____2562
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2565 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2565
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2569 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2569 (FStar_String.concat "; ")
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
           (let uu____2637 = f x in
            FStar_Util.string_builder_append strb uu____2637);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb "; ";
                (let uu____2644 = f x1 in
                 FStar_Util.string_builder_append strb uu____2644)) xs;
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
           (let uu____2677 = f x in
            FStar_Util.string_builder_append strb uu____2677);
           FStar_List.iter
             (fun x1  ->
                FStar_Util.string_builder_append strb ", ";
                (let uu____2684 = f x1 in
                 FStar_Util.string_builder_append strb uu____2684)) xs;
           FStar_Util.string_builder_append strb "}";
           FStar_Util.string_of_string_builder strb)