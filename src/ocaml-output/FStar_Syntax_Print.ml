open Prims
let rec delta_depth_to_string:
  FStar_Syntax_Syntax.delta_depth -> Prims.string =
  fun uu___201_4  ->
    match uu___201_4 with
    | FStar_Syntax_Syntax.Delta_constant  -> "Delta_constant"
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        let uu____6 = FStar_Util.string_of_int i in
        Prims.strcat "Delta_defined_at_level " uu____6
    | FStar_Syntax_Syntax.Delta_equational  -> "Delta_equational"
    | FStar_Syntax_Syntax.Delta_abstract d ->
        let uu____8 =
          let uu____9 = delta_depth_to_string d in Prims.strcat uu____9 ")" in
        Prims.strcat "Delta_abstract (" uu____8
let sli: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____14 = FStar_Options.print_real_names () in
    if uu____14
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let lid_to_string: FStar_Ident.lid -> Prims.string = fun l  -> sli l
let fv_to_string: FStar_Syntax_Syntax.fv -> Prims.string =
  fun fv  ->
    lid_to_string (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let bv_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____28 =
      let uu____29 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "#" uu____29 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____28
let nm_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____34 = FStar_Options.print_real_names () in
    if uu____34
    then bv_to_string bv
    else (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
let db_to_string: FStar_Syntax_Syntax.bv -> Prims.string =
  fun bv  ->
    let uu____40 =
      let uu____41 = FStar_Util.string_of_int bv.FStar_Syntax_Syntax.index in
      Prims.strcat "@" uu____41 in
    Prims.strcat (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText uu____40
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
let is_prim_op ps f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      FStar_All.pipe_right ps
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
  | uu____123 -> false
let get_lid f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____138 -> failwith "get_lid"
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
type exp = FStar_Syntax_Syntax.term
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
let is_inr uu___202_195 =
  match uu___202_195 with
  | FStar_Util.Inl uu____198 -> false
  | FStar_Util.Inr uu____199 -> true
let filter_imp a =
  FStar_All.pipe_right a
    (FStar_List.filter
       (fun uu___203_235  ->
          match uu___203_235 with
          | (uu____239,FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Implicit uu____240)) -> false
          | uu____242 -> true))
let rec reconstruct_lex:
  exp ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.list FStar_Pervasives_Native.option
  =
  fun e  ->
    let uu____254 =
      let uu____255 = FStar_Syntax_Subst.compress e in
      uu____255.FStar_Syntax_Syntax.n in
    match uu____254 with
    | FStar_Syntax_Syntax.Tm_app (f,args) ->
        let args1 = filter_imp args in
        let exps = FStar_List.map FStar_Pervasives_Native.fst args1 in
        let uu____301 =
          (is_lex_cons f) &&
            ((FStar_List.length exps) = (Prims.parse_int "2")) in
        if uu____301
        then
          let uu____312 =
            let uu____317 = FStar_List.nth exps (Prims.parse_int "1") in
            reconstruct_lex uu____317 in
          (match uu____312 with
           | FStar_Pervasives_Native.Some xs ->
               let uu____331 =
                 let uu____335 = FStar_List.nth exps (Prims.parse_int "0") in
                 uu____335 :: xs in
               FStar_Pervasives_Native.Some uu____331
           | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
        else FStar_Pervasives_Native.None
    | uu____355 ->
        let uu____356 = is_lex_top e in
        if uu____356
        then FStar_Pervasives_Native.Some []
        else FStar_Pervasives_Native.None
let rec find f l =
  match l with
  | [] -> failwith "blah"
  | hd1::tl1 ->
      let uu____395 = f hd1 in if uu____395 then hd1 else find f tl1
let find_lid:
  FStar_Ident.lident ->
    (FStar_Ident.lident,Prims.string) FStar_Pervasives_Native.tuple2
      Prims.list -> Prims.string
  =
  fun x  ->
    fun xs  ->
      let uu____411 =
        find
          (fun p  -> FStar_Ident.lid_equals x (FStar_Pervasives_Native.fst p))
          xs in
      FStar_Pervasives_Native.snd uu____411
let infix_prim_op_to_string e =
  let uu____433 = get_lid e in find_lid uu____433 infix_prim_ops
let unary_prim_op_to_string e =
  let uu____447 = get_lid e in find_lid uu____447 unary_prim_ops
let quant_to_string t =
  let uu____461 = get_lid t in find_lid uu____461 quants
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____470) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____473 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____478) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____488 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____488
let lbname_to_string: FStar_Syntax_Syntax.lbname -> Prims.string =
  fun uu___204_492  ->
    match uu___204_492 with
    | FStar_Util.Inl l -> bv_to_string l
    | FStar_Util.Inr l ->
        lid_to_string (l.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let tag_of_term: FStar_Syntax_Syntax.term -> Prims.string =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar x ->
        let uu____500 = db_to_string x in Prims.strcat "Tm_bvar: " uu____500
    | FStar_Syntax_Syntax.Tm_name x ->
        let uu____502 = nm_to_string x in Prims.strcat "Tm_name: " uu____502
    | FStar_Syntax_Syntax.Tm_fvar x ->
        let uu____504 =
          lid_to_string (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        Prims.strcat "Tm_fvar: " uu____504
    | FStar_Syntax_Syntax.Tm_uinst uu____505 -> "Tm_uinst"
    | FStar_Syntax_Syntax.Tm_constant uu____510 -> "Tm_constant"
    | FStar_Syntax_Syntax.Tm_type uu____511 -> "Tm_type"
    | FStar_Syntax_Syntax.Tm_abs uu____512 -> "Tm_abs"
    | FStar_Syntax_Syntax.Tm_arrow uu____522 -> "Tm_arrow"
    | FStar_Syntax_Syntax.Tm_refine uu____530 -> "Tm_refine"
    | FStar_Syntax_Syntax.Tm_app uu____535 -> "Tm_app"
    | FStar_Syntax_Syntax.Tm_match uu____545 -> "Tm_match"
    | FStar_Syntax_Syntax.Tm_ascribed uu____560 -> "Tm_ascribed"
    | FStar_Syntax_Syntax.Tm_let uu____578 -> "Tm_let"
    | FStar_Syntax_Syntax.Tm_uvar uu____586 -> "Tm_uvar"
    | FStar_Syntax_Syntax.Tm_delayed (uu____597,m) ->
        let uu____623 = FStar_ST.read m in
        (match uu____623 with
         | FStar_Pervasives_Native.None  -> "Tm_delayed"
         | FStar_Pervasives_Native.Some uu____634 -> "Tm_delayed-resolved")
    | FStar_Syntax_Syntax.Tm_meta uu____639 -> "Tm_meta"
    | FStar_Syntax_Syntax.Tm_unknown  -> "Tm_unknown"
let uvar_to_string: FStar_Syntax_Syntax.uvar -> Prims.string =
  fun u  ->
    let uu____648 = FStar_Options.hide_uvar_nums () in
    if uu____648
    then "?"
    else
      (let uu____650 =
         let uu____651 = FStar_Syntax_Unionfind.uvar_id u in
         FStar_All.pipe_right uu____651 FStar_Util.string_of_int in
       Prims.strcat "?" uu____650)
let version_to_string: FStar_Syntax_Syntax.version -> Prims.string =
  fun v1  ->
    let uu____656 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.major in
    let uu____657 = FStar_Util.string_of_int v1.FStar_Syntax_Syntax.minor in
    FStar_Util.format2 "%s.%s" uu____656 uu____657
let univ_uvar_to_string: FStar_Syntax_Syntax.universe_uvar -> Prims.string =
  fun u  ->
    let uu____662 = FStar_Options.hide_uvar_nums () in
    if uu____662
    then "?"
    else
      (let uu____664 =
         let uu____665 =
           let uu____666 = FStar_Syntax_Unionfind.univ_uvar_id u in
           FStar_All.pipe_right uu____666 FStar_Util.string_of_int in
         let uu____667 =
           let uu____668 = version_to_string (FStar_Pervasives_Native.snd u) in
           Prims.strcat ":" uu____668 in
         Prims.strcat uu____665 uu____667 in
       Prims.strcat "?" uu____664)
let rec int_of_univ:
  Prims.int ->
    FStar_Syntax_Syntax.universe ->
      (Prims.int,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun n1  ->
    fun u  ->
      let uu____682 = FStar_Syntax_Subst.compress_univ u in
      match uu____682 with
      | FStar_Syntax_Syntax.U_zero  -> (n1, FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.U_succ u1 ->
          int_of_univ (n1 + (Prims.parse_int "1")) u1
      | uu____688 -> (n1, (FStar_Pervasives_Native.Some u))
let rec univ_to_string: FStar_Syntax_Syntax.universe -> Prims.string =
  fun u  ->
    let uu____694 =
      let uu____695 = FStar_Options.ugly () in Prims.op_Negation uu____695 in
    if uu____694
    then
      let e = FStar_Syntax_Resugar.resugar_universe u FStar_Range.dummyRange in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let uu____699 = FStar_Syntax_Subst.compress_univ u in
       match uu____699 with
       | FStar_Syntax_Syntax.U_unif u1 -> univ_uvar_to_string u1
       | FStar_Syntax_Syntax.U_name x -> x.FStar_Ident.idText
       | FStar_Syntax_Syntax.U_bvar x ->
           let uu____707 = FStar_Util.string_of_int x in
           Prims.strcat "@" uu____707
       | FStar_Syntax_Syntax.U_zero  -> "0"
       | FStar_Syntax_Syntax.U_succ u1 ->
           let uu____709 = int_of_univ (Prims.parse_int "1") u1 in
           (match uu____709 with
            | (n1,FStar_Pervasives_Native.None ) ->
                FStar_Util.string_of_int n1
            | (n1,FStar_Pervasives_Native.Some u2) ->
                let uu____718 = univ_to_string u2 in
                let uu____719 = FStar_Util.string_of_int n1 in
                FStar_Util.format2 "(%s + %s)" uu____718 uu____719)
       | FStar_Syntax_Syntax.U_max us ->
           let uu____722 =
             let uu____723 = FStar_List.map univ_to_string us in
             FStar_All.pipe_right uu____723 (FStar_String.concat ", ") in
           FStar_Util.format1 "(max %s)" uu____722
       | FStar_Syntax_Syntax.U_unknown  -> "unknown")
let univs_to_string: FStar_Syntax_Syntax.universe Prims.list -> Prims.string
  =
  fun us  ->
    let uu____732 = FStar_List.map univ_to_string us in
    FStar_All.pipe_right uu____732 (FStar_String.concat ", ")
let univ_names_to_string: FStar_Ident.ident Prims.list -> Prims.string =
  fun us  ->
    let uu____741 = FStar_List.map (fun x  -> x.FStar_Ident.idText) us in
    FStar_All.pipe_right uu____741 (FStar_String.concat ", ")
let qual_to_string: FStar_Syntax_Syntax.qualifier -> Prims.string =
  fun uu___205_749  ->
    match uu___205_749 with
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
        let uu____751 = lid_to_string l in
        FStar_Util.format1 "(Discriminator %s)" uu____751
    | FStar_Syntax_Syntax.Projector (l,x) ->
        let uu____754 = lid_to_string l in
        FStar_Util.format2 "(Projector %s %s)" uu____754 x.FStar_Ident.idText
    | FStar_Syntax_Syntax.RecordType (ns,fns) ->
        let uu____761 =
          let uu____762 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____762 in
        let uu____764 =
          let uu____765 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____765 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordType %s %s)" uu____761 uu____764
    | FStar_Syntax_Syntax.RecordConstructor (ns,fns) ->
        let uu____776 =
          let uu____777 = FStar_Ident.path_of_ns ns in
          FStar_Ident.text_of_path uu____777 in
        let uu____779 =
          let uu____780 =
            FStar_All.pipe_right fns (FStar_List.map FStar_Ident.text_of_id) in
          FStar_All.pipe_right uu____780 (FStar_String.concat ", ") in
        FStar_Util.format2 "(RecordConstructor %s %s)" uu____776 uu____779
    | FStar_Syntax_Syntax.Action eff_lid ->
        let uu____786 = lid_to_string eff_lid in
        FStar_Util.format1 "(Action %s)" uu____786
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
    | uu____794 ->
        let uu____796 =
          FStar_All.pipe_right quals (FStar_List.map qual_to_string) in
        FStar_All.pipe_right uu____796 (FStar_String.concat " ")
let quals_to_string':
  FStar_Syntax_Syntax.qualifier Prims.list -> Prims.string =
  fun quals  ->
    match quals with
    | [] -> ""
    | uu____807 ->
        let uu____809 = quals_to_string quals in Prims.strcat uu____809 " "
let rec term_to_string: FStar_Syntax_Syntax.term -> Prims.string =
  fun x  ->
    let uu____857 =
      let uu____858 = FStar_Options.ugly () in Prims.op_Negation uu____858 in
    if uu____857
    then
      let e = FStar_Syntax_Resugar.resugar_term x in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (let x1 = FStar_Syntax_Subst.compress x in
       let x2 =
         let uu____864 = FStar_Options.print_implicits () in
         if uu____864 then x1 else FStar_Syntax_Util.unmeta x1 in
       match x2.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____866 -> failwith "impossible"
       | FStar_Syntax_Syntax.Tm_app (uu____881,[]) -> failwith "Empty args!"
       | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern ps)
           ->
           let pats =
             let uu____908 =
               FStar_All.pipe_right ps
                 (FStar_List.map
                    (fun args  ->
                       let uu____926 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____937  ->
                                 match uu____937 with
                                 | (t1,uu____941) -> term_to_string t1)) in
                       FStar_All.pipe_right uu____926
                         (FStar_String.concat "; "))) in
             FStar_All.pipe_right uu____908 (FStar_String.concat "\\/") in
           let uu____944 = term_to_string t in
           FStar_Util.format2 "{:pattern %s} %s" pats uu____944
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
           let uu____956 = tag_of_term t in
           let uu____957 = sli m in
           let uu____958 = term_to_string t' in
           let uu____959 = term_to_string t in
           FStar_Util.format4 "(Monadic-%s{%s %s} %s)" uu____956 uu____957
             uu____958 uu____959
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_monadic_lift (m0,m1,t')) ->
           let uu____972 = tag_of_term t in
           let uu____973 = term_to_string t' in
           let uu____974 = sli m0 in
           let uu____975 = sli m1 in
           let uu____976 = term_to_string t in
           FStar_Util.format5 "(MonadicLift-%s{%s : %s -> %s} %s)" uu____972
             uu____973 uu____974 uu____975 uu____976
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_alien (uu____978,s)) ->
           FStar_Util.format1 "(Meta_alien \"%s\")" s
       | FStar_Syntax_Syntax.Tm_meta
           (t,FStar_Syntax_Syntax.Meta_labeled (l,r,b)) when
           FStar_Options.print_implicits () ->
           let uu____992 = FStar_Range.string_of_range r in
           let uu____993 = term_to_string t in
           FStar_Util.format3 "Meta_labeled(%s, %s){%s}" l uu____992
             uu____993
       | FStar_Syntax_Syntax.Tm_meta (t,uu____995) -> term_to_string t
       | FStar_Syntax_Syntax.Tm_bvar x3 ->
           let uu____1001 = db_to_string x3 in
           let uu____1002 =
             let uu____1003 = tag_of_term x3.FStar_Syntax_Syntax.sort in
             Prims.strcat ":" uu____1003 in
           Prims.strcat uu____1001 uu____1002
       | FStar_Syntax_Syntax.Tm_name x3 -> nm_to_string x3
       | FStar_Syntax_Syntax.Tm_fvar f -> fv_to_string f
       | FStar_Syntax_Syntax.Tm_uvar (u,uu____1007) -> uvar_to_string u
       | FStar_Syntax_Syntax.Tm_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Tm_type u ->
           let uu____1026 = FStar_Options.print_universes () in
           if uu____1026
           then
             let uu____1027 = univ_to_string u in
             FStar_Util.format1 "Type u#(%s)" uu____1027
           else "Type"
       | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
           let uu____1041 = binders_to_string " -> " bs in
           let uu____1042 = comp_to_string c in
           FStar_Util.format2 "(%s -> %s)" uu____1041 uu____1042
       | FStar_Syntax_Syntax.Tm_abs (bs,t2,lc) ->
           (match lc with
            | FStar_Pervasives_Native.Some rc when
                FStar_Options.print_implicits () ->
                let uu____1059 = binders_to_string " " bs in
                let uu____1060 = term_to_string t2 in
                let uu____1061 =
                  if FStar_Option.isNone rc.FStar_Syntax_Syntax.residual_typ
                  then "None"
                  else
                    (let uu____1065 =
                       FStar_Option.get rc.FStar_Syntax_Syntax.residual_typ in
                     term_to_string uu____1065) in
                FStar_Util.format4 "(fun %s -> (%s $$ (residual) %s %s))"
                  uu____1059 uu____1060
                  (rc.FStar_Syntax_Syntax.residual_effect).FStar_Ident.str
                  uu____1061
            | uu____1068 ->
                let uu____1070 = binders_to_string " " bs in
                let uu____1071 = term_to_string t2 in
                FStar_Util.format2 "(fun %s -> %s)" uu____1070 uu____1071)
       | FStar_Syntax_Syntax.Tm_refine (xt,f) ->
           let uu____1078 = bv_to_string xt in
           let uu____1079 =
             FStar_All.pipe_right xt.FStar_Syntax_Syntax.sort term_to_string in
           let uu____1082 = FStar_All.pipe_right f formula_to_string in
           FStar_Util.format3 "(%s:%s{%s})" uu____1078 uu____1079 uu____1082
       | FStar_Syntax_Syntax.Tm_app (t,args) ->
           let uu____1101 = term_to_string t in
           let uu____1102 = args_to_string args in
           FStar_Util.format2 "(%s %s)" uu____1101 uu____1102
       | FStar_Syntax_Syntax.Tm_let (lbs,e) ->
           let uu____1115 = lbs_to_string [] lbs in
           let uu____1116 = term_to_string e in
           FStar_Util.format2 "%s\nin\n%s" uu____1115 uu____1116
       | FStar_Syntax_Syntax.Tm_ascribed (e,(annot,topt),eff_name) ->
           let annot1 =
             match annot with
             | FStar_Util.Inl t ->
                 let uu____1164 =
                   let uu____1165 =
                     FStar_Util.map_opt eff_name FStar_Ident.text_of_lid in
                   FStar_All.pipe_right uu____1165
                     (FStar_Util.dflt "default") in
                 let uu____1168 = term_to_string t in
                 FStar_Util.format2 "[%s] %s" uu____1164 uu____1168
             | FStar_Util.Inr c -> comp_to_string c in
           let topt1 =
             match topt with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some t ->
                 let uu____1184 = term_to_string t in
                 FStar_Util.format1 "by %s" uu____1184 in
           let uu____1185 = term_to_string e in
           FStar_Util.format3 "(%s <ascribed: %s %s)" uu____1185 annot1 topt1
       | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
           let uu____1212 = term_to_string head1 in
           let uu____1213 =
             let uu____1214 =
               FStar_All.pipe_right branches
                 (FStar_List.map
                    (fun uu____1238  ->
                       match uu____1238 with
                       | (p,wopt,e) ->
                           let uu____1248 =
                             FStar_All.pipe_right p pat_to_string in
                           let uu____1249 =
                             match wopt with
                             | FStar_Pervasives_Native.None  -> ""
                             | FStar_Pervasives_Native.Some w ->
                                 let uu____1251 =
                                   FStar_All.pipe_right w term_to_string in
                                 FStar_Util.format1 "when %s" uu____1251 in
                           let uu____1252 =
                             FStar_All.pipe_right e term_to_string in
                           FStar_Util.format3 "%s %s -> %s" uu____1248
                             uu____1249 uu____1252)) in
             FStar_Util.concat_l "\n\t|" uu____1214 in
           FStar_Util.format2 "(match %s with\n\t| %s)" uu____1212 uu____1213
       | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
           let uu____1259 = FStar_Options.print_universes () in
           if uu____1259
           then
             let uu____1260 = term_to_string t in
             let uu____1261 = univs_to_string us in
             FStar_Util.format2 "%s<%s>" uu____1260 uu____1261
           else term_to_string t
       | uu____1263 -> tag_of_term x2)
and pat_to_string: FStar_Syntax_Syntax.pat -> Prims.string =
  fun x  ->
    let uu____1265 =
      let uu____1266 = FStar_Options.ugly () in Prims.op_Negation uu____1266 in
    if uu____1265
    then
      let e = FStar_Syntax_Resugar.resugar_pat x in
      let d = FStar_Parser_ToDocument.pat_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match x.FStar_Syntax_Syntax.v with
       | FStar_Syntax_Syntax.Pat_cons (l,pats) ->
           let uu____1280 = fv_to_string l in
           let uu____1281 =
             let uu____1282 =
               FStar_List.map
                 (fun uu____1290  ->
                    match uu____1290 with
                    | (x1,b) ->
                        let p = pat_to_string x1 in
                        if b then Prims.strcat "#" p else p) pats in
             FStar_All.pipe_right uu____1282 (FStar_String.concat " ") in
           FStar_Util.format2 "(%s %s)" uu____1280 uu____1281
       | FStar_Syntax_Syntax.Pat_dot_term (x1,uu____1299) ->
           let uu____1304 = FStar_Options.print_bound_var_types () in
           if uu____1304
           then
             let uu____1305 = bv_to_string x1 in
             let uu____1306 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 ".%s:%s" uu____1305 uu____1306
           else
             (let uu____1308 = bv_to_string x1 in
              FStar_Util.format1 ".%s" uu____1308)
       | FStar_Syntax_Syntax.Pat_var x1 ->
           let uu____1310 = FStar_Options.print_bound_var_types () in
           if uu____1310
           then
             let uu____1311 = bv_to_string x1 in
             let uu____1312 = term_to_string x1.FStar_Syntax_Syntax.sort in
             FStar_Util.format2 "%s:%s" uu____1311 uu____1312
           else bv_to_string x1
       | FStar_Syntax_Syntax.Pat_constant c -> const_to_string c
       | FStar_Syntax_Syntax.Pat_wild x1 ->
           let uu____1316 = FStar_Options.print_real_names () in
           if uu____1316
           then
             let uu____1317 = bv_to_string x1 in
             Prims.strcat "Pat_wild " uu____1317
           else "_")
and lbs_to_string:
  FStar_Syntax_Syntax.qualifier Prims.list ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun quals  ->
    fun lbs  ->
      let lbs1 =
        let uu____1329 = FStar_Options.print_universes () in
        if uu____1329
        then
          let uu____1333 =
            FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
              (FStar_List.map
                 (fun lb  ->
                    let uu____1347 =
                      let uu____1350 =
                        FStar_Syntax_Util.mk_conj
                          lb.FStar_Syntax_Syntax.lbtyp
                          lb.FStar_Syntax_Syntax.lbdef in
                      FStar_Syntax_Subst.open_univ_vars
                        lb.FStar_Syntax_Syntax.lbunivs uu____1350 in
                    match uu____1347 with
                    | (us,td) ->
                        let uu____1353 =
                          let uu____1360 =
                            let uu____1361 = FStar_Syntax_Subst.compress td in
                            uu____1361.FStar_Syntax_Syntax.n in
                          match uu____1360 with
                          | FStar_Syntax_Syntax.Tm_app
                              (uu____1370,(t,uu____1372)::(d,uu____1374)::[])
                              -> (t, d)
                          | uu____1408 -> failwith "Impossibe" in
                        (match uu____1353 with
                         | (t,d) ->
                             let uu___212_1425 = lb in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___212_1425.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = us;
                               FStar_Syntax_Syntax.lbtyp = t;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___212_1425.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = d
                             }))) in
          ((FStar_Pervasives_Native.fst lbs), uu____1333)
        else lbs in
      let uu____1429 = quals_to_string' quals in
      let uu____1430 =
        let uu____1431 =
          FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs1)
            (FStar_List.map
               (fun lb  ->
                  let uu____1442 =
                    lbname_to_string lb.FStar_Syntax_Syntax.lbname in
                  let uu____1443 =
                    let uu____1444 = FStar_Options.print_universes () in
                    if uu____1444
                    then
                      let uu____1445 =
                        let uu____1446 =
                          univ_names_to_string lb.FStar_Syntax_Syntax.lbunivs in
                        Prims.strcat uu____1446 ">" in
                      Prims.strcat "<" uu____1445
                    else "" in
                  let uu____1448 =
                    term_to_string lb.FStar_Syntax_Syntax.lbtyp in
                  let uu____1449 =
                    FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbdef
                      term_to_string in
                  FStar_Util.format4 "%s %s : %s = %s" uu____1442 uu____1443
                    uu____1448 uu____1449)) in
        FStar_Util.concat_l "\n and " uu____1431 in
      FStar_Util.format3 "%slet %s %s" uu____1429
        (if FStar_Pervasives_Native.fst lbs1 then "rec" else "") uu____1430
and lcomp_to_string: FStar_Syntax_Syntax.lcomp -> Prims.string =
  fun lc  ->
    let uu____1455 = FStar_Options.print_effect_args () in
    if uu____1455
    then
      let uu____1456 = lc.FStar_Syntax_Syntax.comp () in
      comp_to_string uu____1456
    else
      (let uu____1458 = sli lc.FStar_Syntax_Syntax.eff_name in
       let uu____1459 = term_to_string lc.FStar_Syntax_Syntax.res_typ in
       FStar_Util.format2 "%s %s" uu____1458 uu____1459)
and imp_to_string:
  Prims.string ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      Prims.string
  =
  fun s  ->
    fun uu___206_1461  ->
      match uu___206_1461 with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (false ))
          -> Prims.strcat "#" s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true ))
          -> Prims.strcat "#." s
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) ->
          Prims.strcat "$" s
      | uu____1463 -> s
and binder_to_string':
  Prims.bool -> FStar_Syntax_Syntax.binder -> Prims.string =
  fun is_arrow  ->
    fun b  ->
      let uu____1467 =
        let uu____1468 = FStar_Options.ugly () in
        Prims.op_Negation uu____1468 in
      if uu____1467
      then
        let e = FStar_Syntax_Resugar.resugar_binder b FStar_Range.dummyRange in
        let d = FStar_Parser_ToDocument.binder_to_document e in
        FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
          (Prims.parse_int "100") d
      else
        (let uu____1472 = b in
         match uu____1472 with
         | (a,imp) ->
             let uu____1475 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____1475
             then
               let uu____1476 = term_to_string a.FStar_Syntax_Syntax.sort in
               Prims.strcat "_:" uu____1476
             else
               (let uu____1478 =
                  (Prims.op_Negation is_arrow) &&
                    (let uu____1480 = FStar_Options.print_bound_var_types () in
                     Prims.op_Negation uu____1480) in
                if uu____1478
                then
                  let uu____1481 = nm_to_string a in
                  imp_to_string uu____1481 imp
                else
                  (let uu____1483 =
                     let uu____1484 = nm_to_string a in
                     let uu____1485 =
                       let uu____1486 =
                         term_to_string a.FStar_Syntax_Syntax.sort in
                       Prims.strcat ":" uu____1486 in
                     Prims.strcat uu____1484 uu____1485 in
                   imp_to_string uu____1483 imp)))
and binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' false b
and arrow_binder_to_string: FStar_Syntax_Syntax.binder -> Prims.string =
  fun b  -> binder_to_string' true b
and binders_to_string:
  Prims.string -> FStar_Syntax_Syntax.binders -> Prims.string =
  fun sep  ->
    fun bs  ->
      let bs1 =
        let uu____1492 = FStar_Options.print_implicits () in
        if uu____1492 then bs else filter_imp bs in
      if sep = " -> "
      then
        let uu____1494 =
          FStar_All.pipe_right bs1 (FStar_List.map arrow_binder_to_string) in
        FStar_All.pipe_right uu____1494 (FStar_String.concat sep)
      else
        (let uu____1499 =
           FStar_All.pipe_right bs1 (FStar_List.map binder_to_string) in
         FStar_All.pipe_right uu____1499 (FStar_String.concat sep))
and arg_to_string:
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.arg_qualifier
                              FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun uu___207_1503  ->
    match uu___207_1503 with
    | (a,imp) ->
        let uu____1511 = term_to_string a in imp_to_string uu____1511 imp
and args_to_string: FStar_Syntax_Syntax.args -> Prims.string =
  fun args  ->
    let args1 =
      let uu____1514 = FStar_Options.print_implicits () in
      if uu____1514 then args else filter_imp args in
    let uu____1518 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string) in
    FStar_All.pipe_right uu____1518 (FStar_String.concat " ")
and comp_to_string: FStar_Syntax_Syntax.comp -> Prims.string =
  fun c  ->
    let uu____1526 =
      let uu____1527 = FStar_Options.ugly () in Prims.op_Negation uu____1527 in
    if uu____1526
    then
      let e = FStar_Syntax_Resugar.resugar_comp c in
      let d = FStar_Parser_ToDocument.term_to_document e in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d
    else
      (match c.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Total (t,uopt) ->
           let uu____1539 =
             let uu____1540 = FStar_Syntax_Subst.compress t in
             uu____1540.FStar_Syntax_Syntax.n in
           (match uu____1539 with
            | FStar_Syntax_Syntax.Tm_type uu____1543 when
                let uu____1544 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1544 -> term_to_string t
            | uu____1545 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1547 = univ_to_string u in
                     let uu____1548 = term_to_string t in
                     FStar_Util.format2 "Tot<%s> %s" uu____1547 uu____1548
                 | uu____1549 ->
                     let uu____1551 = term_to_string t in
                     FStar_Util.format1 "Tot %s" uu____1551))
       | FStar_Syntax_Syntax.GTotal (t,uopt) ->
           let uu____1560 =
             let uu____1561 = FStar_Syntax_Subst.compress t in
             uu____1561.FStar_Syntax_Syntax.n in
           (match uu____1560 with
            | FStar_Syntax_Syntax.Tm_type uu____1564 when
                let uu____1565 =
                  (FStar_Options.print_implicits ()) ||
                    (FStar_Options.print_universes ()) in
                Prims.op_Negation uu____1565 -> term_to_string t
            | uu____1566 ->
                (match uopt with
                 | FStar_Pervasives_Native.Some u when
                     FStar_Options.print_universes () ->
                     let uu____1568 = univ_to_string u in
                     let uu____1569 = term_to_string t in
                     FStar_Util.format2 "GTot<%s> %s" uu____1568 uu____1569
                 | uu____1570 ->
                     let uu____1572 = term_to_string t in
                     FStar_Util.format1 "GTot %s" uu____1572))
       | FStar_Syntax_Syntax.Comp c1 ->
           let basic =
             let uu____1575 = FStar_Options.print_effect_args () in
             if uu____1575
             then
               let uu____1576 = sli c1.FStar_Syntax_Syntax.effect_name in
               let uu____1577 =
                 let uu____1578 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.comp_univs
                     (FStar_List.map univ_to_string) in
                 FStar_All.pipe_right uu____1578 (FStar_String.concat ", ") in
               let uu____1582 =
                 term_to_string c1.FStar_Syntax_Syntax.result_typ in
               let uu____1583 =
                 let uu____1584 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map arg_to_string) in
                 FStar_All.pipe_right uu____1584 (FStar_String.concat ", ") in
               let uu____1596 =
                 let uu____1597 =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map cflags_to_string) in
                 FStar_All.pipe_right uu____1597 (FStar_String.concat " ") in
               FStar_Util.format5 "%s<%s> (%s) %s (attributes %s)" uu____1576
                 uu____1577 uu____1582 uu____1583 uu____1596
             else
               (let uu____1603 =
                  (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___208_1606  ->
                           match uu___208_1606 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | uu____1607 -> false)))
                    &&
                    (let uu____1609 = FStar_Options.print_effect_args () in
                     Prims.op_Negation uu____1609) in
                if uu____1603
                then
                  let uu____1610 =
                    term_to_string c1.FStar_Syntax_Syntax.result_typ in
                  FStar_Util.format1 "Tot %s" uu____1610
                else
                  (let uu____1612 =
                     ((let uu____1615 = FStar_Options.print_effect_args () in
                       Prims.op_Negation uu____1615) &&
                        (let uu____1617 = FStar_Options.print_implicits () in
                         Prims.op_Negation uu____1617))
                       &&
                       (FStar_Ident.lid_equals
                          c1.FStar_Syntax_Syntax.effect_name
                          FStar_Parser_Const.effect_ML_lid) in
                   if uu____1612
                   then term_to_string c1.FStar_Syntax_Syntax.result_typ
                   else
                     (let uu____1619 =
                        (let uu____1622 = FStar_Options.print_effect_args () in
                         Prims.op_Negation uu____1622) &&
                          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                             (FStar_Util.for_some
                                (fun uu___209_1625  ->
                                   match uu___209_1625 with
                                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                                   | uu____1626 -> false))) in
                      if uu____1619
                      then
                        let uu____1627 =
                          term_to_string c1.FStar_Syntax_Syntax.result_typ in
                        FStar_Util.format1 "ALL %s" uu____1627
                      else
                        (let uu____1629 =
                           sli c1.FStar_Syntax_Syntax.effect_name in
                         let uu____1630 =
                           term_to_string c1.FStar_Syntax_Syntax.result_typ in
                         FStar_Util.format2 "%s (%s)" uu____1629 uu____1630)))) in
           let dec =
             let uu____1632 =
               FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                 (FStar_List.collect
                    (fun uu___210_1639  ->
                       match uu___210_1639 with
                       | FStar_Syntax_Syntax.DECREASES e ->
                           let uu____1644 =
                             let uu____1645 = term_to_string e in
                             FStar_Util.format1 " (decreases %s)" uu____1645 in
                           [uu____1644]
                       | uu____1646 -> [])) in
             FStar_All.pipe_right uu____1632 (FStar_String.concat " ") in
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
    | FStar_Syntax_Syntax.DECREASES uu____1649 -> ""
and formula_to_string:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> Prims.string
  = fun phi  -> term_to_string phi
let enclose_universes: Prims.string -> Prims.string =
  fun s  ->
    let uu____1659 = FStar_Options.print_universes () in
    if uu____1659 then Prims.strcat "<" (Prims.strcat s ">") else ""
let tscheme_to_string: FStar_Syntax_Syntax.tscheme -> Prims.string =
  fun s  ->
    let uu____1665 =
      let uu____1666 = FStar_Options.ugly () in Prims.op_Negation uu____1666 in
    if uu____1665
    then
      let d = FStar_Syntax_Resugar.resugar_tscheme s in
      let d1 = FStar_Parser_ToDocument.decl_to_document d in
      FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
        (Prims.parse_int "100") d1
    else
      (let uu____1670 = s in
       match uu____1670 with
       | (us,t) ->
           let uu____1675 =
             let uu____1676 = univ_names_to_string us in
             FStar_All.pipe_left enclose_universes uu____1676 in
           let uu____1677 = term_to_string t in
           FStar_Util.format2 "%s%s" uu____1675 uu____1677)
let action_to_string: FStar_Syntax_Syntax.action -> Prims.string =
  fun a  ->
    let uu____1682 = sli a.FStar_Syntax_Syntax.action_name in
    let uu____1683 =
      binders_to_string " " a.FStar_Syntax_Syntax.action_params in
    let uu____1684 =
      let uu____1685 =
        univ_names_to_string a.FStar_Syntax_Syntax.action_univs in
      FStar_All.pipe_left enclose_universes uu____1685 in
    let uu____1686 = term_to_string a.FStar_Syntax_Syntax.action_typ in
    let uu____1687 = term_to_string a.FStar_Syntax_Syntax.action_defn in
    FStar_Util.format5 "%s%s %s : %s = %s" uu____1682 uu____1683 uu____1684
      uu____1686 uu____1687
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
          let uu____1706 =
            let uu____1707 = FStar_Options.ugly () in
            Prims.op_Negation uu____1707 in
          if uu____1706
          then
            let d = FStar_Syntax_Resugar.resugar_eff_decl for_free r q ed in
            let d1 = FStar_Parser_ToDocument.decl_to_document d in
            FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
              (Prims.parse_int "100") d1
          else
            (let actions_to_string actions =
               let uu____1717 =
                 FStar_All.pipe_right actions
                   (FStar_List.map action_to_string) in
               FStar_All.pipe_right uu____1717 (FStar_String.concat ",\n\t") in
             let uu____1722 =
               let uu____1724 =
                 let uu____1726 = lid_to_string ed.FStar_Syntax_Syntax.mname in
                 let uu____1727 =
                   let uu____1729 =
                     let uu____1730 =
                       univ_names_to_string ed.FStar_Syntax_Syntax.univs in
                     FStar_All.pipe_left enclose_universes uu____1730 in
                   let uu____1731 =
                     let uu____1733 =
                       binders_to_string " " ed.FStar_Syntax_Syntax.binders in
                     let uu____1734 =
                       let uu____1736 =
                         term_to_string ed.FStar_Syntax_Syntax.signature in
                       let uu____1737 =
                         let uu____1739 =
                           tscheme_to_string ed.FStar_Syntax_Syntax.ret_wp in
                         let uu____1740 =
                           let uu____1742 =
                             tscheme_to_string ed.FStar_Syntax_Syntax.bind_wp in
                           let uu____1743 =
                             let uu____1745 =
                               tscheme_to_string
                                 ed.FStar_Syntax_Syntax.if_then_else in
                             let uu____1746 =
                               let uu____1748 =
                                 tscheme_to_string
                                   ed.FStar_Syntax_Syntax.ite_wp in
                               let uu____1749 =
                                 let uu____1751 =
                                   tscheme_to_string
                                     ed.FStar_Syntax_Syntax.stronger in
                                 let uu____1752 =
                                   let uu____1754 =
                                     tscheme_to_string
                                       ed.FStar_Syntax_Syntax.close_wp in
                                   let uu____1755 =
                                     let uu____1757 =
                                       tscheme_to_string
                                         ed.FStar_Syntax_Syntax.assert_p in
                                     let uu____1758 =
                                       let uu____1760 =
                                         tscheme_to_string
                                           ed.FStar_Syntax_Syntax.assume_p in
                                       let uu____1761 =
                                         let uu____1763 =
                                           tscheme_to_string
                                             ed.FStar_Syntax_Syntax.null_wp in
                                         let uu____1764 =
                                           let uu____1766 =
                                             tscheme_to_string
                                               ed.FStar_Syntax_Syntax.trivial in
                                           let uu____1767 =
                                             let uu____1769 =
                                               term_to_string
                                                 ed.FStar_Syntax_Syntax.repr in
                                             let uu____1770 =
                                               let uu____1772 =
                                                 tscheme_to_string
                                                   ed.FStar_Syntax_Syntax.bind_repr in
                                               let uu____1773 =
                                                 let uu____1775 =
                                                   tscheme_to_string
                                                     ed.FStar_Syntax_Syntax.return_repr in
                                                 let uu____1776 =
                                                   let uu____1778 =
                                                     actions_to_string
                                                       ed.FStar_Syntax_Syntax.actions in
                                                   [uu____1778] in
                                                 uu____1775 :: uu____1776 in
                                               uu____1772 :: uu____1773 in
                                             uu____1769 :: uu____1770 in
                                           uu____1766 :: uu____1767 in
                                         uu____1763 :: uu____1764 in
                                       uu____1760 :: uu____1761 in
                                     uu____1757 :: uu____1758 in
                                   uu____1754 :: uu____1755 in
                                 uu____1751 :: uu____1752 in
                               uu____1748 :: uu____1749 in
                             uu____1745 :: uu____1746 in
                           uu____1742 :: uu____1743 in
                         uu____1739 :: uu____1740 in
                       uu____1736 :: uu____1737 in
                     uu____1733 :: uu____1734 in
                   uu____1729 :: uu____1731 in
                 uu____1726 :: uu____1727 in
               (if for_free then "_for_free " else "") :: uu____1724 in
             FStar_Util.format
               "new_effect%s { %s%s %s : %s \n  return_wp   = %s\n; bind_wp     = %s\n; if_then_else= %s\n; ite_wp      = %s\n; stronger    = %s\n; close_wp    = %s\n; assert_p    = %s\n; assume_p    = %s\n; null_wp     = %s\n; trivial     = %s\n; repr        = %s\n; bind_repr   = %s\n; return_repr = %s\nand effect_actions\n\t%s\n}\n"
               uu____1722)
let eff_decl_to_string:
  Prims.bool -> FStar_Syntax_Syntax.eff_decl -> Prims.string =
  fun for_free  ->
    fun ed  -> eff_decl_to_string' for_free FStar_Range.dummyRange [] ed
let rec sigelt_to_string: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    let uu____1792 =
      let uu____1793 = FStar_Options.ugly () in Prims.op_Negation uu____1793 in
    if uu____1792
    then
      let e = FStar_Syntax_Resugar.resugar_sigelt x in
      match e with
      | FStar_Pervasives_Native.Some d ->
          let d1 = FStar_Parser_ToDocument.decl_to_document d in
          FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") d1
      | uu____1798 -> ""
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
           (lid,univs1,tps,k,uu____1807,uu____1808) ->
           let uu____1813 = quals_to_string' x.FStar_Syntax_Syntax.sigquals in
           let uu____1814 = binders_to_string " " tps in
           let uu____1815 = term_to_string k in
           FStar_Util.format4 "%stype %s %s : %s" uu____1813
             lid.FStar_Ident.str uu____1814 uu____1815
       | FStar_Syntax_Syntax.Sig_datacon
           (lid,univs1,t,uu____1819,uu____1820,uu____1821) ->
           let uu____1824 = FStar_Options.print_universes () in
           if uu____1824
           then
             let uu____1825 = FStar_Syntax_Subst.open_univ_vars univs1 t in
             (match uu____1825 with
              | (univs2,t1) ->
                  let uu____1830 = univ_names_to_string univs2 in
                  let uu____1831 = term_to_string t1 in
                  FStar_Util.format3 "datacon<%s> %s : %s" uu____1830
                    lid.FStar_Ident.str uu____1831)
           else
             (let uu____1833 = term_to_string t in
              FStar_Util.format2 "datacon %s : %s" lid.FStar_Ident.str
                uu____1833)
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) ->
           let uu____1837 = FStar_Syntax_Subst.open_univ_vars univs1 t in
           (match uu____1837 with
            | (univs2,t1) ->
                let uu____1842 =
                  quals_to_string' x.FStar_Syntax_Syntax.sigquals in
                let uu____1843 =
                  let uu____1844 = FStar_Options.print_universes () in
                  if uu____1844
                  then
                    let uu____1845 = univ_names_to_string univs2 in
                    FStar_Util.format1 "<%s>" uu____1845
                  else "" in
                let uu____1847 = term_to_string t1 in
                FStar_Util.format4 "%sval %s %s : %s" uu____1842
                  lid.FStar_Ident.str uu____1843 uu____1847)
       | FStar_Syntax_Syntax.Sig_assume (lid,uu____1849,f) ->
           let uu____1851 = term_to_string f in
           FStar_Util.format2 "val %s : %s" lid.FStar_Ident.str uu____1851
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____1853,uu____1854) ->
           lbs_to_string x.FStar_Syntax_Syntax.sigquals lbs
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____1860 = term_to_string e in
           FStar_Util.format1 "let _ = %s" uu____1860
       | FStar_Syntax_Syntax.Sig_bundle (ses,uu____1862) ->
           let uu____1867 = FStar_List.map sigelt_to_string ses in
           FStar_All.pipe_right uu____1867 (FStar_String.concat "\n")
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
             | (FStar_Pervasives_Native.Some lift_wp,uu____1879) -> lift_wp
             | (uu____1883,FStar_Pervasives_Native.Some lift) -> lift in
           let uu____1888 =
             FStar_Syntax_Subst.open_univ_vars
               (FStar_Pervasives_Native.fst lift_wp)
               (FStar_Pervasives_Native.snd lift_wp) in
           (match uu____1888 with
            | (us,t) ->
                let uu____1895 = lid_to_string se.FStar_Syntax_Syntax.source in
                let uu____1896 = lid_to_string se.FStar_Syntax_Syntax.target in
                let uu____1897 = univ_names_to_string us in
                let uu____1898 = term_to_string t in
                FStar_Util.format4 "sub_effect %s ~> %s : <%s> %s" uu____1895
                  uu____1896 uu____1897 uu____1898)
       | FStar_Syntax_Syntax.Sig_effect_abbrev (l,univs1,tps,c,flags) ->
           let uu____1906 = FStar_Options.print_universes () in
           if uu____1906
           then
             let uu____1907 =
               let uu____1910 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_arrow (tps, c))
                   FStar_Pervasives_Native.None FStar_Range.dummyRange in
               FStar_Syntax_Subst.open_univ_vars univs1 uu____1910 in
             (match uu____1907 with
              | (univs2,t) ->
                  let uu____1917 =
                    let uu____1925 =
                      let uu____1926 = FStar_Syntax_Subst.compress t in
                      uu____1926.FStar_Syntax_Syntax.n in
                    match uu____1925 with
                    | FStar_Syntax_Syntax.Tm_arrow (bs,c1) -> (bs, c1)
                    | uu____1953 -> failwith "impossible" in
                  (match uu____1917 with
                   | (tps1,c1) ->
                       let uu____1973 = sli l in
                       let uu____1974 = univ_names_to_string univs2 in
                       let uu____1975 = binders_to_string " " tps1 in
                       let uu____1976 = comp_to_string c1 in
                       FStar_Util.format4 "effect %s<%s> %s = %s" uu____1973
                         uu____1974 uu____1975 uu____1976))
           else
             (let uu____1978 = sli l in
              let uu____1979 = binders_to_string " " tps in
              let uu____1980 = comp_to_string c in
              FStar_Util.format3 "effect %s %s = %s" uu____1978 uu____1979
                uu____1980))
let format_error: FStar_Range.range -> Prims.string -> Prims.string =
  fun r  ->
    fun msg  ->
      let uu____1989 = FStar_Range.string_of_range r in
      FStar_Util.format2 "%s: %s\n" uu____1989 msg
let rec sigelt_to_string_short: FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun x  ->
    match x.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        ((uu____1994,{ FStar_Syntax_Syntax.lbname = lb;
                       FStar_Syntax_Syntax.lbunivs = uu____1996;
                       FStar_Syntax_Syntax.lbtyp = t;
                       FStar_Syntax_Syntax.lbeff = uu____1998;
                       FStar_Syntax_Syntax.lbdef = uu____1999;_}::[]),uu____2000,uu____2001)
        ->
        let uu____2017 = lbname_to_string lb in
        let uu____2018 = term_to_string t in
        FStar_Util.format2 "let %s : %s" uu____2017 uu____2018
    | uu____2019 ->
        let uu____2020 =
          FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt x)
            (FStar_List.map (fun l  -> l.FStar_Ident.str)) in
        FStar_All.pipe_right uu____2020 (FStar_String.concat ", ")
let rec modul_to_string: FStar_Syntax_Syntax.modul -> Prims.string =
  fun m  ->
    let uu____2031 = sli m.FStar_Syntax_Syntax.name in
    let uu____2032 =
      let uu____2033 =
        FStar_List.map sigelt_to_string m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____2033 (FStar_String.concat "\n") in
    FStar_Util.format2 "module %s\n%s" uu____2031 uu____2032
let subst_elt_to_string: FStar_Syntax_Syntax.subst_elt -> Prims.string =
  fun uu___211_2039  ->
    match uu___211_2039 with
    | FStar_Syntax_Syntax.DB (i,x) ->
        let uu____2042 = FStar_Util.string_of_int i in
        let uu____2043 = bv_to_string x in
        FStar_Util.format2 "DB (%s, %s)" uu____2042 uu____2043
    | FStar_Syntax_Syntax.NM (x,i) ->
        let uu____2046 = bv_to_string x in
        let uu____2047 = FStar_Util.string_of_int i in
        FStar_Util.format2 "NM (%s, %s)" uu____2046 uu____2047
    | FStar_Syntax_Syntax.NT (x,t) ->
        let uu____2054 = bv_to_string x in
        let uu____2055 = term_to_string t in
        FStar_Util.format2 "DB (%s, %s)" uu____2054 uu____2055
    | FStar_Syntax_Syntax.UN (i,u) ->
        let uu____2058 = FStar_Util.string_of_int i in
        let uu____2059 = univ_to_string u in
        FStar_Util.format2 "UN (%s, %s)" uu____2058 uu____2059
    | FStar_Syntax_Syntax.UD (u,i) ->
        let uu____2062 = FStar_Util.string_of_int i in
        FStar_Util.format2 "UD (%s, %s)" u.FStar_Ident.idText uu____2062
let subst_to_string: FStar_Syntax_Syntax.subst_t -> Prims.string =
  fun s  ->
    let uu____2067 =
      FStar_All.pipe_right s (FStar_List.map subst_elt_to_string) in
    FStar_All.pipe_right uu____2067 (FStar_String.concat "; ")
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
let list_to_string f elts =
  match elts with
  | [] -> "[]"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "[";
       (let uu____2121 = f x in
        FStar_Util.string_builder_append strb uu____2121);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb "; ";
            (let uu____2128 = f x1 in
             FStar_Util.string_builder_append strb uu____2128)) xs;
       FStar_Util.string_builder_append strb "]";
       FStar_Util.string_of_string_builder strb)
let set_to_string f s =
  let elts = FStar_Util.set_elements s in
  match elts with
  | [] -> "{}"
  | x::xs ->
      let strb = FStar_Util.new_string_builder () in
      (FStar_Util.string_builder_append strb "{";
       (let uu____2160 = f x in
        FStar_Util.string_builder_append strb uu____2160);
       FStar_List.iter
         (fun x1  ->
            FStar_Util.string_builder_append strb ", ";
            (let uu____2167 = f x1 in
             FStar_Util.string_builder_append strb uu____2167)) xs;
       FStar_Util.string_builder_append strb "}";
       FStar_Util.string_of_string_builder strb)